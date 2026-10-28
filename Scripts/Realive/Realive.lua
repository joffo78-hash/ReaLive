-- @description Realive — système de cues pour REAPER
-- @version 1.0
-- @author joffo78-hash
-- @about
--   Realive est un système de lancement de cues pour REAPER.
--   Nécessite REAPER et ReaImGui. La compatibilité multiplateforme
--   et la fonction OSC restent à vérifier avant une annonce publique.
-- @changelog
--   Première version préparée pour l'indexation ReaPack.
--

-- ActionList.lua
-- Playlist d'actions type QLab pour REAPER (ReaImGui)
-- Types : CUE, STOP, PRESET, OSC, MIDI

if not reaper.ImGui_CreateContext then
  reaper.MB("ReaImGui n'est pas installé.\nInstallez-le via ReaPack.", "ActionList", 0)
  return
end

-- Fenêtre volontairement non dockable : elle s'ouvre comme fenêtre flottante.
-- Ne pas activer ImGui_ConfigFlags_DockingEnable ici.
local ctx = reaper.ImGui_CreateContext("Actions")

local EXT = "ACTIONLIST"
local PROJ = reaper.EnumProjects(-1)

-- MIDI via piste relais + Virtual Keyboard (StuffMIDIMessage).
-- Une seule piste "ActionList MIDI" écoute le VKB ; des sends MIDI only
-- routent vers les pistes instruments (qui gardent leur input normal).
local MIDI_NOTE_DURATION_MS = 100
local MIDI_VKB_RECINPUT = 6112 -- Virtual MIDI Keyboard, tous canaux
local MIDI_RELAY_NAME = "ActionList MIDI"
local midi_note_offs = {} -- note-offs différés {t=, status=, note=}
local midi_relay_dests = {} -- guid → MediaTrack (sends actifs depuis la relais)

-- Variables globales pour isoler le zoom de la forme d'onde
local wave_rect_x1, wave_rect_y1, wave_rect_x2, wave_rect_y2 = nil, nil, nil, nil

---------------------------------------------------------------- OSC (Mavriq Lua Sockets)
local socket, osc_encode
local has_socket = false
local socket_init_status = "OSC désactivé : installer/mettre à jour Mavriq Lua Sockets 1.2 via ReaPack."

do
  local resource = reaper.GetResourcePath()
  local roots = {
    resource .. "/Scripts/Mavriq ReaScript Repository/Various/Mavriq-Lua-Sockets",
    resource .. "/Scripts/Mavriq-Lua-Sockets",
  }
  local socket_root
  for _, root in ipairs(roots) do
    local f = io.open(root .. "/socket/core.dll", "rb")
    if f then
      f:close()
      socket_root = root
      break
    end
  end
  if socket_root then
    package.cpath = socket_root .. "/?.dll;" .. package.cpath
    package.path = socket_root .. "/?.lua;" .. socket_root .. "/?/init.lua;" .. package.path
    local ok, sock = pcall(require, "socket.core")
    if ok and type(sock) == "table" and type(sock.udp) == "function" then
      socket = sock
      has_socket = true
      socket_init_status = "OSC disponible (Mavriq Lua Sockets : " .. socket_root .. ")."
      osc_encode = function(address, args)
        local function pad(s)
          local n = 4 - (#s % 4)
          if n == 4 then n = 0 end
          return s .. string.rep("\0", n)
        end
        local msg = pad(address or "/")
        local tags = ","
        local data = ""
        for _, v in ipairs(args or {}) do
          if type(v) == "number" then
            if v == math.floor(v) and math.abs(v) < 2147483648 then
              tags = tags .. "i"
              data = data .. string.pack(">i4", v)
            else
              tags = tags .. "f"
              data = data .. string.pack(">f", v)
            end
          else
            tags = tags .. "s"
            data = data .. pad(tostring(v))
          end
        end
        return pad(msg) .. pad(tags) .. data
      end
    else
      socket_init_status = "OSC désactivé : Mavriq Lua Sockets trouvé, mais socket.core n'a pas pu être chargé. Vérifier que la version installée est 1.2."
      if not ok then
        socket_init_status = socket_init_status .. " Détail Lua : " .. tostring(sock)
      end
    end
  end
end

---------------------------------------------------------------- État
local actions, next_id = {}, 1
-- Cue lists (onglets). `actions` reste un alias de la liste active pour préserver l'éditeur existant.
local tabs = {{name = "Liste 1", actions = actions}}
local active_tab = 1
local tab_name_edit, tab_name_buffer = nil, ""
local pending_delete_tab = nil
local cue_clipboard, clipboard_cut = nil, false
local function sync_active_tab()
  if not tabs or #tabs == 0 then tabs = {{name = "Liste 1", actions = {}}} end
  active_tab = math.max(1, math.min(active_tab or 1, #tabs))
  actions = tabs[active_tab].actions
end
local function new_tab_name()
  return "Liste " .. tostring(#tabs + 1)
end
local function clone_table(value)
  if type(value) ~= "table" then return value end
  local out = {}
  for k, v in pairs(value) do out[clone_table(k)] = clone_table(v) end
  return out
end
local selected = nil -- cue préparée pour GO/clavier
local editor_selected = nil -- cue dont les paramètres sont affichés
local picked, pick_anchor = {}, nil
local status = has_socket and "Prêt (OSC disponible)." or ("Prêt. " .. socket_init_status)
local file_drop_api_warning_shown = false
local margin = tonumber(reaper.GetExtState(EXT, "margin")) or 200
local fades, morphs = {}, {}
local del_jobs = {}
local marked = {}
local HOLD = 1.0
local ui_scale = tonumber(reaper.GetExtState(EXT, "zoom")) or 1.0
local lower_h = 240
local lower_h_override = nil

local function S(x) return math.floor(x * ui_scale + 0.5) end
local function set_zoom(z)
  ui_scale = math.max(0.6, math.min(2.5, z))
  reaper.SetExtState(EXT, "zoom", string.format("%.3f", ui_scale), true)
end

local runs = {}
local wave_cache = {}
local wf_drag, cv_drag = nil, nil
local marker_drag = nil
-- Devamp clignotant (runtime, par cue id).
local devamp_flags = {} -- [id] = true
local play_check, np_runs, last_run_tick = nil, nil, 0
local LOOP_HORIZON = 6.0
local active_ids, last_active_scan = {}, 0
local stop_until = {}
-- Enchaînement automatique : compte à rebours de la cue source vers la suivante.
local auto_chain = nil
local ext_runs = {}
local ANTICLICK = 0.03
local stop_fade = tonumber(reaper.GetExtState(EXT, "stopfade")) or 1.0

local prefs = {
  auto_stop       = false,
  delete_on_stop  = true,
  exclusive_track = true,
  ports           = {},
}

local cue_session, np_since, last_scan, idle_since = false, nil, 0, nil
-- Position d'origine de la session (curseur d'édition au moment du GO).
-- Sur STOP avec Delete on stop, la tête de lecture y revient.
local session_origin = nil
local actions_by_id = {}
local X = {} -- aides regroupées (limite Lua : 200 variables locales)
local apply_snap
local fire
local default_track_guid
local delete_cuelist_items
local delete_all_cuelist_items

local item_props = {"D_LENGTH","D_VOL","D_FADEINLEN","D_FADEOUTLEN","D_FADEINSHAPE","D_FADEOUTSHAPE","D_SNAPOFFSET"}
local take_props = {"D_STARTOFFS","D_VOL","D_PAN","D_PLAYRATE","D_PITCH"}

---------------------------------------------------------------- Sérialisation
local function ser(v)
  local t = type(v)
  if t == "table" then
    local parts = {}
    for k, x in pairs(v) do parts[#parts+1] = "["..ser(k).."]="..ser(x) end
    return "{"..table.concat(parts,",").."}"
  elseif t == "string" then return string.format("%q", v)
  elseif t == "number" then return string.format("%.17g", v)
  else return tostring(v) end
end

local function rebuild_id_map()
  actions_by_id = {}
  for _, tab in ipairs(tabs or {}) do
    for _, a in ipairs(tab.actions or {}) do
      actions_by_id[a.id] = a
      actions_by_id[tostring(a.id)] = a
      local numeric_id = tonumber(a.id)
      if numeric_id then actions_by_id[numeric_id] = a end
    end
  end
end

-- Historique des modifications (états sérialisés, sans inclure l'historique lui-même).
local undo_stack, redo_stack = {}, {}
local history_last = nil
local history_restoring = false
local HISTORY_LIMIT = 100

local function current_data_string()
  return ser({ actions = actions, tabs = tabs, active_tab = active_tab, next_id = next_id, prefs = prefs })
end

local function save()
  local data = current_data_string()
  if not history_restoring and history_last and data ~= history_last then
    undo_stack[#undo_stack + 1] = history_last
    if #undo_stack > HISTORY_LIMIT then table.remove(undo_stack, 1) end
    redo_stack = {}
  end
  reaper.SetProjExtState(PROJ, EXT, "data", data)
  history_last = data
  rebuild_id_map()
end

local function restore_history_state(data)
  local loader = load("return " .. data, "actionlist_history", "t", {})
  if not loader then return false end
  local ok, d = pcall(loader)
  if not ok or type(d) ~= "table" or type(d.actions) ~= "table" then return false end
  history_restoring = true
  next_id = d.next_id or 1
  if type(d.tabs) == "table" and #d.tabs > 0 then
    tabs = d.tabs
    for _, tab in ipairs(tabs) do tab.name = tab.name or "Liste"; tab.actions = tab.actions or {} end
    active_tab = d.active_tab or 1
    sync_active_tab()
  else
    actions = d.actions or {}
    tabs = {{name = "Liste 1", actions = actions}}
    active_tab = 1
    sync_active_tab()
  end
  if type(d.prefs) == "table" then
    for k, v in pairs(d.prefs) do prefs[k] = v end
  end
  prefs.ports = prefs.ports or {}
  rebuild_id_map()
  local encoded = current_data_string()
  reaper.SetProjExtState(PROJ, EXT, "data", encoded)
  history_last = encoded
  history_restoring = false
  picked, pick_anchor, marked, selected = {}, nil, {}, nil
      editor_selected = nil
  return true
end

local function undo_change()
  if #undo_stack == 0 then status = "Rien à annuler."; return end
  redo_stack[#redo_stack + 1] = current_data_string()
  local previous = table.remove(undo_stack)
  if restore_history_state(previous) then status = "Modification annulée." end
end

local function redo_change()
  if #redo_stack == 0 then status = "Rien à rétablir."; return end
  undo_stack[#undo_stack + 1] = current_data_string()
  local following = table.remove(redo_stack)
  if restore_history_state(following) then status = "Modification rétablie." end
end

local function load_data()
  local _, s = reaper.GetProjExtState(PROJ, EXT, "data")
  if s and s ~= "" then
    local f = load("return "..s, "data", "t", {})
    if f then
      local ok, d = pcall(f)
      if ok and type(d) == "table" then
        next_id  = d.next_id or 1
        if type(d.tabs) == "table" and #d.tabs > 0 then
          tabs = d.tabs
          for _, tab in ipairs(tabs) do tab.name = tab.name or "Liste"; tab.actions = tab.actions or {} end
          active_tab = d.active_tab or 1
          sync_active_tab()
        else
          actions = d.actions or {}
          tabs = {{name = "Liste 1", actions = actions}}
          active_tab = 1
          sync_active_tab()
        end
        if type(d.prefs) == "table" then
          for k,v in pairs(d.prefs) do prefs[k] = v end
        end
        if not prefs.ports then prefs.ports = {} end
        -- Forcer des booléens stricts (évite "true" string / 1 qui cassent la case à cocher).
        prefs.delete_on_stop = prefs.delete_on_stop and true or false
        prefs.auto_stop = prefs.auto_stop and true or false
        prefs.exclusive_track = prefs.exclusive_track ~= false
        for _, a in ipairs(actions) do
          if a.type == "fade" then
            a.type, a.track, a.targets = "stop", nil, nil
            a.dur = a.dur or 1.0
          end
        end
      end
    end
  end
  rebuild_id_map()
end

---------------------------------------------------------------- Utilitaires
local function is_playing()
  return (math.floor(reaper.GetPlayStateEx(PROJ)) & 1) ~= 0
end

local function now_pos()
  return is_playing() and reaper.GetPlayPosition2Ex(PROJ) or reaper.GetCursorPositionEx(PROJ)
end

local function track_name(tr)
  local _, n = reaper.GetTrackName(tr)
  return n
end

local function find_track(guid)
  if not guid then return nil end
  for i = 0, reaper.CountTracks(PROJ)-1 do
    local t = reaper.GetTrack(PROJ, i)
    if reaper.GetTrackGUID(t) == guid then return t end
  end
end

local function tracks_of(tr)
  local list = {tr}
  if reaper.GetMediaTrackInfo_Value(tr, "I_FOLDERDEPTH") ~= 1 then return list end
  local depth = 1
  local i = math.floor(reaper.GetMediaTrackInfo_Value(tr, "IP_TRACKNUMBER"))
  while depth > 0 and i < reaper.CountTracks(PROJ) do
    local t = reaper.GetTrack(PROJ, i)
    list[#list+1] = t
    depth = depth + reaper.GetMediaTrackInfo_Value(t, "I_FOLDERDEPTH")
    i = i + 1
  end
  return list
end

local function get_regions(proj)
  proj = proj or PROJ
  local regs = {}
  local _, nm, nr = reaper.CountProjectMarkers(proj)
  for i = 0, nm+nr-1 do
    local _, isrgn, pos, rgnend, name, idx = reaper.EnumProjectMarkers2(proj, i)
    if isrgn then
      if name == "" then name = "Region "..idx end
      regs[#regs+1] = {name=name, s=pos, e=rgnend, idx=idx}
    end
  end
  return regs
end

local function find_track_by_name(name)
  for i = 0, reaper.CountTracks(PROJ)-1 do
    local t = reaper.GetTrack(PROJ, i)
    if track_name(t) == name then return t end
  end
end

local function other_projects()
  local list, i = {}, 0
  while true do
    local p, fn = reaper.EnumProjects(i)
    if not p then break end
    if p ~= PROJ then
      fn = fn or ""
      list[#list+1] = {
        proj = p, fn = fn,
        label = (fn ~= "" and (fn:match("([^/\\]+)$") or fn)) or "(sans nom)"
      }
    end
    i = i + 1
  end
  return list
end

local function find_project(fn)
  if not fn or fn == "" then return PROJ end
  for _, o in ipairs(other_projects()) do
    if o.fn == fn then return o.proj end
  end
  return nil
end

local function lerp_db(a, b, p)
  if a > 1e-4 and b > 1e-4 then
    local da = 20 * math.log(a, 10)
    local db = 20 * math.log(b, 10)
    return 10 ^ ((da + (db-da)*p) / 20)
  end
  return a + (b-a)*p
end

local function on_main(fn)
  local prev = reaper.EnumProjects(-1)
  if prev ~= PROJ then
    reaper.SelectProjectInstance(PROJ)
    fn()
    reaper.SelectProjectInstance(prev)
  else
    fn()
  end
end

local function play_main()
  -- Mémoriser le point de départ avant de lancer la lecture.
  if not is_playing() then
    session_origin = reaper.GetCursorPositionEx(PROJ)
  end
  on_main(function() reaper.OnPlayButton() end)
  play_check = reaper.time_precise() + 0.5
end

local function stop_main()
  on_main(function() reaper.OnStopButton() end)
end

local function with_proj(p, fn)
  local prev = reaper.EnumProjects(-1)
  if prev ~= p then
    reaper.SelectProjectInstance(p)
    fn()
    reaper.SelectProjectInstance(prev)
  else
    fn()
  end
end

-- Arrête le transport et replace la tête de lecture au point de départ de la session
-- (curseur d'édition au moment du GO), pas à la fin de l'item.
local function stop_here()
  local pos = session_origin
  if pos == nil then pos = reaper.GetCursorPositionEx(PROJ) end
  on_main(function()
    if (math.floor(reaper.GetPlayStateEx(PROJ)) & 1) ~= 0 then
      reaper.OnPauseButton()
    end
    reaper.SetEditCurPos2(PROJ, pos, true, false)
    reaper.OnStopButton()
  end)
end

local function active_cue_items()
  local p = now_pos()
  for i = 0, reaper.CountMediaItems(PROJ)-1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local e = reaper.GetMediaItemInfo_Value(it, "D_POSITION") + reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
    if e > p then
      local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
      if mark == "1" then return true end
    end
  end
  return false
end

---------------------------------------------------------------- Volume / boucles
local function env_gain(env, t)
  local n = env and #env or 0
  if n == 0 then return 1 end
  if t <= env[1].t then return env[1].g end
  if t >= env[n].t then return env[n].g end
  for i = 1, n-1 do
    local p, q = env[i], env[i+1]
    if t <= q.t then
      return lerp_db(p.g, q.g, (t - p.t) / math.max(1e-9, q.t - p.t))
    end
  end
  return 1
end

local function kill_runs(ids)
  if not ids then
    for _, r in pairs(runs) do r.alive = false end
    return
  end
  for _, id in ipairs(ids) do
    if runs[id] then runs[id].alive = false end
  end
end

local function add_file_item(dest, file, pos, tin, seg, fadein, gain, id, markers)
  local src = reaper.PCM_Source_CreateFromFile(file)
  if not src then return nil end
  local new = reaper.AddMediaItemToTrack(dest)
  local ntk = reaper.AddTakeToMediaItem(new)
  reaper.SetMediaItemTake_Source(ntk, src)
  reaper.SetMediaItemTakeInfo_Value(ntk, "D_STARTOFFS", tin)
  reaper.SetMediaItemTakeInfo_Value(ntk, "D_VOL", gain or 1)
  local cue = actions_by_id[id] or actions_by_id[tostring(id)]
  -- D_LENGTH est en temps projet. Avec un playrate, la durée projet doit être
  -- segment_source / vitesse pour que tout le segment soit entendu une seule fois.
  local speed = 1
  if cue then
    local db = tonumber(cue.wave_gain_db) or 0
    reaper.SetMediaItemTakeInfo_Value(ntk, "D_VOL", (gain or 1) * (10 ^ (db / 20)))
    reaper.SetMediaItemTakeInfo_Value(ntk, "D_PAN", math.max(-1, math.min(1, tonumber(cue.wave_pan) or 0)))
    speed = math.max(0.01, math.min(16, tonumber(cue.wave_speed) or 1))
    reaper.SetMediaItemTakeInfo_Value(ntk, "D_PLAYRATE", speed)
    local pitch = tonumber(cue.wave_pitch) or 0
    if cue.wave_pitch_link then pitch = 12 * (math.log(speed) / math.log(2)) end
    reaper.SetMediaItemTakeInfo_Value(ntk, "D_PITCH", pitch)
  end
  local proj_len = math.max(0.001, (tonumber(seg) or 0) / speed)
  reaper.SetMediaItemInfo_Value(new, "D_POSITION", pos)
  reaper.SetMediaItemInfo_Value(new, "D_LENGTH", proj_len)
  reaper.SetMediaItemInfo_Value(new, "D_FADEINLEN", math.min(fadein or 0, proj_len))
  reaper.SetMediaItemInfo_Value(new, "D_FADEOUTLEN", 0)
  if ntk and type(markers) == "table" and reaper.SetTakeMarker then
    local src_start = tonumber(tin) or 0
    local src_end = src_start + (tonumber(seg) or 0)
    for _, marker in ipairs(markers) do
      local mt = tonumber(marker.t)
      local mn = tostring(marker.name or ""):gsub("^%s+", ""):gsub("%s+$", "")
      if mt and mn ~= "" and mt >= src_start - 1e-6 and mt <= src_end + 1e-6 then
        reaper.SetTakeMarker(ntk, -1, mn, mt, tonumber(marker.color) or 0)
      end
    end
  end
  reaper.GetSetMediaItemInfo_String(new, "P_EXT:cuelist", "1", true)
  reaper.GetSetMediaItemInfo_String(new, "P_EXT:cuelist_id", tostring(id), true)
  reaper.UpdateItemInProject(new)
  return new
end

local function copy_take_markers(src_take, dst_take)
  if not src_take or not dst_take or not reaper.GetNumTakeMarkers
     or not reaper.GetTakeMarker or not reaper.SetTakeMarker then return 0 end
  local copied = 0
  for m = 0, reaper.GetNumTakeMarkers(src_take) - 1 do
    local mpos, mname, color = reaper.GetTakeMarker(src_take, m)
    if mpos and mpos >= 0 and mname and mname ~= "" then
      local idx = reaper.SetTakeMarker(dst_take, -1, mname, mpos, color or 0)
      if idx and idx >= 0 then copied = copied + 1 end
    end
  end
  return copied
end

local function refresh_active(now)
  if now - last_active_scan < 0.12 then return end
  last_active_scan = now
  local set = {}
  if is_playing() then
    local p = now_pos()
    for i = 0, reaper.CountMediaItems(PROJ)-1 do
      local it = reaper.GetMediaItem(PROJ, i)
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if pos + len > p then
        local _, id = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
        if id ~= "" then
          local fading = false
          local fo = reaper.GetMediaItemInfo_Value(it, "D_FADEOUTLEN")
          if fo >= 0.02 and pos <= p and p >= pos + len - fo then fading = true end
          if not fading then
            local fj = fades[reaper.GetTrackGUID(reaper.GetMediaItem_Track(it))]
            if fj and not fj.done then fading = true end
          end
          if fading then set[id] = "fade"
          elseif set[id] ~= "fade" then set[id] = "run" end
        end
      end
    end
  end
  for id, r in pairs(ext_runs) do
    set[tostring(id)] = r.stopping and "fade" or "run"
  end
  active_ids = set
end

-- Items audio (hors keepalive MIDI) d'une cue sur sa piste.
local function cue_audio_items(dest, id, fn)
  local sid = tostring(id)
  for i = reaper.CountTrackMediaItems(dest) - 1, 0, -1 do
    local it = reaper.GetTrackMediaItem(dest, i)
    local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
    if cid == sid then
      local tk = reaper.GetActiveTake(it)
      if tk and not reaper.TakeIsMIDI(tk) then fn(it, tk) end
    end
  end
end

-- Supprime les items "keepalive" (MIDI vides posés pendant une pause).
local function remove_keepalive(id)
  local sid = tostring(id)
  for i = reaper.CountMediaItems(PROJ) - 1, 0, -1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, ka = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_keepalive", "", false)
    if ka == "1" then
      local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
      if cid == sid then reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it) end
    end
  end
end

-- Estime le temps source courant d'un run (pause / playhead UI).
-- Source de vérité : l'item de la cue réellement sous la tête de lecture.
local function run_source_time(r, p)
  if not r then return nil end
  local speed = math.max(0.01, r.speed or 1)
  if r.paused and r.pause_src and (not r.pause_proj or p >= r.pause_proj) then return r.pause_src end
  local dest = find_track(r.dest_guid)
  if dest then
    local found
    for i = reaper.CountTrackMediaItems(dest) - 1, 0, -1 do
      local it = reaper.GetTrackMediaItem(dest, i)
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      if pos <= p then
        local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
        if pos + len > p then
          local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
          if cid == tostring(r.id) then
            local tk = reaper.GetActiveTake(it)
            if tk and not reaper.TakeIsMIDI(tk) then
              local so = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS")
              local rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE")
              found = so + (p - pos) * (rate > 0 and rate or speed)
              break
            end
          end
        end
      end
    end
    if found then return math.min(r.tout or found, found) end
  end
  -- Repli (aucun item sous la playhead : trou ou fin)
  local tin, li, lo, tout = r.tin, r.li or r.tin, r.lo or (r.tin + r.seg), r.tout or (r.tin + r.seg)
  if r.release_end and p >= r.release_end then return tout end
  local elapsed = (p - (r.t0 or p)) * speed
  if elapsed < 0 then return tin end
  if not r.loop then return math.min(tout, tin + elapsed) end
  local intro = math.max(0.001, lo - tin)
  if elapsed <= intro then return tin + elapsed end
  local cycle = math.max(0.001, lo - li)
  return li + ((elapsed - intro) % cycle)
end

-- Planifie la suite Lo → OUT à la position projet `at` (sans interruption).
local function schedule_release(r, dest, at)
  local speed = math.max(0.01, r.speed or 1)
  local lo, tout = r.lo, r.tout
  local rel_seg = math.max(0, tout - lo)
  if rel_seg > 0.005 then
    local gain = (r.env and #r.env > 0) and env_gain(r.env, lo) or 1
    add_file_item(dest, r.file, at, lo, rel_seg, 0, gain, r.id, r.markers)
  end
  r.phase = "release"
  r.release_start = at
  r.release_end = at + rel_seg / speed
  r.next = r.release_end
  reaper.UpdateArrange()
end

-- Réapplique IN/OUT/Li/Lo/vitesse à une cue en boucle déjà lancée, SANS
-- écraser la structure des items (intro In→Lo, cycles Li→Lo, suite Lo→OUT).
-- L'item sous la playhead est recoupé, les items futurs sont supprimés et
-- re-planifiés par process_runs.
local function replan_loop_run(a, r)
  if not (r and r.loop and r.alive and not r.paused) then return end
  local dest = find_track(r.dest_guid)
  if not dest then return end
  local old_lo = r.lo
  r.tin, r.tout = a.inpt, a.outpt
  r.li = math.max(r.tin, math.min(tonumber(a.loop_in) or r.tin, r.tout - 0.01))
  r.lo = math.max(r.li + 0.01, math.min(tonumber(a.loop_out) or r.tout, r.tout))
  r.seg = r.lo - r.li
  r.speed = math.max(0.01, math.min(16, tonumber(a.wave_speed) or 1))
  r.env = a.env or r.env or {}
  r.markers = a.markers or r.markers or {}
  local speed = r.speed
  local p = now_pos()
  local cur, cur_pos, cur_so
  local future = {}
  cue_audio_items(dest, r.id, function(it, tk)
    local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
    local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
    local so  = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS")
    if pos <= p and pos + len > p then
      cur, cur_pos, cur_so = it, pos, so
    elseif pos > p then
      future[#future+1] = {it, so}
    end
  end)
  for _, f in ipairs(future) do
    if old_lo and math.abs(f[2] - old_lo) > 1e-6 and (r.loops_done or 0) > 0 then
      r.loops_done = r.loops_done - 1 -- passage planifié jamais joué
    end
    reaper.DeleteTrackMediaItem(dest, f[1])
  end
  if cur then
    local is_release = old_lo and math.abs(cur_so - old_lo) < 1e-6
    local src_now = cur_so + (p - cur_pos) * speed
    local end_src, passed = r.lo, false
    if is_release then end_src = r.tout
    elseif src_now >= r.lo - 0.01 then end_src, passed = r.tout, true end
    local len = math.max(0.01, (end_src - cur_so) / speed)
    reaper.SetMediaItemInfo_Value(cur, "D_LENGTH", len)
    reaper.SetMediaItemInfo_Value(cur, "D_FADEOUTLEN", 0)
    reaper.UpdateItemInProject(cur)
    r.next = cur_pos + len
    if is_release or passed then
      r.phase = "release"
      r.release_start = is_release and r.release_start or p
      r.release_end = r.next
    elseif r.phase == "release" then
      schedule_release(r, dest, r.next)
    end
  else
    r.next = p + margin / 1000
    if r.phase == "release" then schedule_release(r, dest, r.next) end
  end
  -- gains (enveloppe + gain de cue) sur les items conservés
  local db = tonumber(a.wave_gain_db) or 0
  cue_audio_items(dest, r.id, function(it, tk)
    local so = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS")
    local g = (r.env and #r.env > 0) and env_gain(r.env, so) or 1
    reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", g * (10 ^ (db / 20)))
    reaper.UpdateItemInProject(it)
  end)
  reaper.UpdateArrange()
end

-- Résout la liste d'IDs ciblés d'une action (Q1,Q8…). nil = toutes les cues.
local function resolve_targets(a)
  local ids, seen = {}, {}
  if type(a.targets_text) == "string" and a.targets_text:match("%S") then
    for token in (a.targets_text .. ","):gmatch("(.-),") do
      local digits = token:match("^%s*[Qq]?(%d+)%s*$")
      if digits then
        local id = tonumber(digits)
        if not seen[id] then ids[#ids+1] = id; seen[id] = true end
      end
    end
  elseif a.targets and #a.targets > 0 then
    for _, id in ipairs(a.targets) do
      id = tonumber(id) or id
      if not seen[id] then ids[#ids+1] = id; seen[id] = true end
    end
  end
  if #ids == 0 then return nil end
  return ids
end

-- Les passages sont planifiés ≤ LOOP_HORIZON à l'avance : un fade de pause plus
-- long n'aurait pas d'item sur lequel s'appliquer.
local PAUSE_FADE_MAX = 5.0

-- Met la cue en pause (sans toucher au transport). Fade out optionnel AVANT la pause.
-- Retourne true si une action a été appliquée (sinon : déjà en pause / rien en cours).
local function pause_run(id, fade)
  local r = runs[id]
  if not r or not r.alive or r.paused then return false end
  local dest = find_track(r.dest_guid)
  local p = now_pos()
  local F = math.max(0, math.min(PAUSE_FADE_MAX, tonumber(fade) or 0))
  local t_end, src_end = p + F, nil
  if F > 0 then
    cue_audio_items(dest, id, function(it, tk)
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if pos <= t_end and pos + len > t_end then
        local so = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS")
        local rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE")
        src_end = so + (t_end - pos) * (rate > 0 and rate or (r.speed or 1))
      end
    end)
    if not src_end then F, t_end = 0, p end -- rien de planifié si loin : pause directe
  end
  if not src_end then src_end = run_source_time(r, p) or r.tin end
  r.paused = true
  r.pause_src = src_end
  r.pause_proj = t_end
  if dest then
    local to_del, to_cut = {}, {}
    local lo_ref = r.lo or r.tout
    cue_audio_items(dest, id, function(it, tk)
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if pos >= t_end - 1e-6 then
        to_del[#to_del+1] = it
        -- Passage Li→Lo planifié mais jamais joué : pas décompté du quota.
        local so = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS")
        if r.loop and lo_ref and math.abs(so - lo_ref) > 1e-6 and (r.loops_done or 0) > 0 then
          r.loops_done = r.loops_done - 1
        end
      elseif pos + len > t_end then
        to_cut[#to_cut+1] = {it, pos}
      end
    end)
    for _, it in ipairs(to_del) do reaper.DeleteTrackMediaItem(dest, it) end
    for _, c in ipairs(to_cut) do
      local newlen = math.max(0.01, t_end - c[2])
      reaper.SetMediaItemInfo_Value(c[1], "D_LENGTH", newlen)
      reaper.SetMediaItemInfo_Value(c[1], "D_FADEOUTLEN", F > 0 and math.min(F, newlen) or 0.01)
    end
    -- Garde-fou : un item MIDI vide empêche REAPER de s'arrêter en fin de projet.
    remove_keepalive(id)
    local ka = reaper.CreateNewMIDIItemInProj(dest, t_end, t_end + 3600, false)
    if ka then
      reaper.GetSetMediaItemInfo_String(ka, "P_EXT:cuelist", "1", true)
      reaper.GetSetMediaItemInfo_String(ka, "P_EXT:cuelist_id", tostring(id), true)
      reaper.GetSetMediaItemInfo_String(ka, "P_EXT:cuelist_keepalive", "1", true)
    end
    reaper.UpdateArrange()
  end
  status = string.format("Pause cue Q%s à %.3f s (source)%s.", tostring(id), src_end,
    F > 0 and string.format(", fade out %.1f s", F) or "")
  return true
end

-- Reprend la cue (fade in optionnel). Retourne true si une action a été appliquée.
local function resume_run(id, fade)
  local r = runs[id]
  if not r or not r.alive or not r.paused then return false end
  local dest = find_track(r.dest_guid)
  local src = tonumber(r.pause_src) or r.tin
  local speed = math.max(0.01, r.speed or 1)
  local lo = r.lo or r.tout
  local tout = r.tout or lo
  local li = r.li or r.tin
  local end_src, resume_phase
  if r.phase == "release" or r.devamp or r.devamp_armed then
    end_src = tout
    resume_phase = "release"
  elseif r.loop then
    end_src = math.max(src + 0.01, lo)
    if src >= lo - 1e-4 then src = li; end_src = lo end
    resume_phase = "loop"
  else
    end_src = tout
    resume_phase = "once"
  end
  local seg = math.max(0.01, end_src - src)
  local was_playing = is_playing()
  -- Ne pas chevaucher un fade de pause encore en cours.
  local place = math.max(now_pos() + margin/1000, tonumber(r.pause_proj) or 0)
  remove_keepalive(id)
  if dest then
    local gain = (r.env and #r.env > 0) and env_gain(r.env, src) or 1
    local fi = math.max(0, tonumber(fade) or 0)
    add_file_item(dest, r.file, place, src, seg, math.min(fi, seg / speed), gain, id, r.markers)
    r.next = place + seg / speed
    r.phase = resume_phase
    if resume_phase == "release" then
      r.release_end = r.next
      r.release_start = place + math.max(0, lo - src) / speed
    end
    r.t0 = place - (src - (r.tin or 0)) / speed
    reaper.UpdateArrange()
    if not was_playing then
      reaper.SetEditCurPos2(PROJ, place, false, false)
      reaper.OnPlayButton()
    end
  end
  r.paused = false
  r.pause_src, r.pause_proj = nil, nil
  status = string.format("Reprise cue Q%s à %.3f s (source).", tostring(id), src)
  return true
end

-- Arme le Devamp. Retourne true si armé, false si impossible / déjà armé.
local function devamp_run(id)
  local r = runs[id]
  if not r or not r.alive or not r.loop then return false end
  if r.phase == "release" or r.devamp or r.devamp_armed then return false end
  r.devamp = true -- le bouton clignote tout de suite
  r.devamp_armed = false -- process_runs coupe les passages planifiés
  devamp_flags[id] = true
  devamp_flags[tostring(id)] = true
  status = string.format("Devamp armé (Q%s) : fin du passage en cours jusqu'à Lo, puis poursuite jusqu'à OUT.", tostring(id))
  return true
end

local function process_runs(now)
  if next(runs) == nil then return end
  if not is_playing() then
    -- Ne pas purger les runs en pause (sinon reprise impossible après ~1.5 s).
    local any_paused = false
    for _, rr in pairs(runs) do
      if rr.paused then any_paused = true; break end
    end
    if not any_paused then
      np_runs = np_runs or now
      if now - np_runs > 1.5 then runs, np_runs = {}, nil end
    else
      np_runs = nil
    end
    return
  end
  np_runs = nil
  if now - last_run_tick < 0.04 then return end
  last_run_tick = now
  local p = now_pos()
  for id, r in pairs(runs) do
    if not r.alive then
      remove_keepalive(id)
      runs[id] = nil
    else
      r.id = id
      local dest = find_track(r.dest_guid)
      if r.paused then
        -- Pause : ne plus étendre, conserver pause_src / pause_proj.
      elseif r.loop and dest then
        local speed = math.max(0.01, r.speed or 1)
        local li = r.li or r.tin
        local lo = r.lo or (r.tin + (r.seg or 0))
        local tout = r.tout or lo
        local cycle = math.max(0.001, lo - li)
        local cycle_proj = cycle / speed
        local want_devamp = r.devamp or r.devamp_armed
          or devamp_flags[id] or devamp_flags[tostring(id)]

        if r.phase == "release" then
          -- Fin du clignotement Devamp dès que la playhead a franchi Lo
          -- (= début de l'item Lo→OUT).
          if (r.devamp or r.devamp_armed) and p >= (r.release_start or 0) then
            r.devamp = false
            r.devamp_armed = false
            devamp_flags[id] = nil
            devamp_flags[tostring(id)] = nil
          end
          if p > (r.release_end or r.next) + 0.15 then
            if prefs.delete_on_stop == true then
              delete_cuelist_items({[tostring(id)] = true})
            end
            runs[id] = nil
            devamp_flags[id] = nil
            devamp_flags[tostring(id)] = nil
          end
        else
          if want_devamp then
            -- DEVAMP : on laisse finir le passage Li→Lo (ou In→Lo) en cours,
            -- on supprime TOUS les passages déjà planifiés après lui, puis on
            -- enchaîne immédiatement Lo→OUT. Aucun saut de playhead.
            r.devamp, r.devamp_armed = true, true
            local cut
            cue_audio_items(dest, id, function(it)
              local e = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
                      + reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
              if e > p + 0.03 and (not cut or e < cut) then cut = e end
            end)
            cut = cut or math.max(r.next or 0, p + margin/1000)
            local to_del = {}
            cue_audio_items(dest, id, function(it)
              if reaper.GetMediaItemInfo_Value(it, "D_POSITION") >= cut - 1e-4 then
                to_del[#to_del+1] = it
              end
            end)
            for _, it in ipairs(to_del) do reaper.DeleteTrackMediaItem(dest, it) end
            schedule_release(r, dest, cut)
          else
            local guard = 0
            while guard < 200 do
              -- Quota atteint : Lo→OUT est planifié tout de suite après le
              -- dernier passage (sinon REAPER s'arrête à la fin du dernier item).
              if r.loop_count and (r.loops_done or 0) >= r.loop_count then
                schedule_release(r, dest, r.next)
                break
              end
              if (r.next or 0) >= p + LOOP_HORIZON then break end
              local gain = (r.env and #r.env > 0) and env_gain(r.env, li) or 1
              add_file_item(dest, r.file, r.next, li, cycle, 0, gain, id, r.markers)
              r.next = r.next + cycle_proj
              r.loops_done = (r.loops_done or 0) + 1
              r.phase = "loop"
              guard = guard + 1
            end
            if guard > 0 then reaper.UpdateArrange() end
          end
        end
      elseif not r.loop and p > r.t0 + (r.proj_seg or r.seg) + 0.15 then
        if prefs.delete_on_stop == true then
          local id_str = tostring(id)
          local past = p - 0.05
          for i = reaper.CountMediaItems(PROJ) - 1, 0, -1 do
            local it = reaper.GetMediaItem(PROJ, i)
            local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
            local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
            if mark == "1" and cid == id_str then
              local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
              local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
              if pos + len <= past then
                reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
              end
            end
          end
          reaper.UpdateArrange()
        end
        runs[id] = nil
      end
      
      -- Suivi dynamique de l'enveloppe sur les items actifs
      if runs[id] and r.env and #r.env > 0 and dest and not r.paused then
        local pe = p + margin/1000
        local speed = math.max(0.01, r.speed or 1)
        for k = reaper.CountTrackMediaItems(dest)-1, 0, -1 do
          local it = reaper.GetTrackMediaItem(dest, k)
          local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
          local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
          if pe >= pos and pe < pos + len then
            local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
            if mark == tostring(id) then
              local tk = reaper.GetActiveTake(it)
              if tk then
                local startoffs = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS") or r.tin
                local rel_t = startoffs + (pe - pos) * speed
                local v = env_gain(r.env, rel_t)
                if math.abs(reaper.GetMediaItemTakeInfo_Value(tk, "D_VOL") - v) > 0.002 then
                  reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", v)
                end
              end
              break
            end
          end
        end
      end
    end
  end
end

---------------------------------------------------------------- Pistes
local chan_cache = {}
local function file_channels(file)
  if chan_cache[file] == nil then
    local src = reaper.PCM_Source_CreateFromFile(file)
    if src then
      chan_cache[file] = reaper.GetMediaSourceNumChannels(src)
      reaper.PCM_Source_Destroy(src)
    else
      chan_cache[file] = false
    end
  end
  return chan_cache[file] or nil
end

local function adjust_channels(tr, n)
  if not tr or not n or n < 1 then return nil end
  local need = n + (n % 2)
  local cur = math.floor(reaper.GetMediaTrackInfo_Value(tr, "I_NCHAN"))
  if need > cur then
    reaper.SetMediaTrackInfo_Value(tr, "I_NCHAN", need)
    return need
  end
  return nil
end

local function create_track(name)
  local idx = reaper.CountTracks(PROJ)
  if reaper.InsertTrackInProject then
    reaper.InsertTrackInProject(PROJ, idx, 0)
  else
    on_main(function() reaper.InsertTrackAtIndex(idx, true) end)
  end
  local tr = reaper.GetTrack(PROJ, idx)
  if tr then reaper.GetSetMediaTrackInfo_String(tr, "P_NAME", name, true) end
  return tr
end

local function replace_on_tracks(tracks, id, target, fade)
  -- `fade` = durée de fondu de l'ancienne cue (= fade-in de la nouvelle, comportement voulu).
  -- Minimum anti-click si fade = 0 pour éviter un clic.
  local t_end = target + math.max(ANTICLICK, tonumber(fade) or 0)
  local sid, stopped = tostring(id), {}
  for _, tr in pairs(tracks) do
    for i = reaper.CountTrackMediaItems(tr)-1, 0, -1 do
      local it = reaper.GetTrackMediaItem(tr, i)
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if pos + len > target then
        local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
        if mark ~= "" and mark ~= sid then
          if pos >= target then
            reaper.DeleteTrackMediaItem(tr, it)
          else
            local new_end = math.min(pos + len, t_end)
            reaper.SetMediaItemInfo_Value(it, "D_LENGTH", new_end - pos)
            reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", new_end - target)
          end
          stopped[#stopped+1] = tonumber(mark)
        end
      end
    end
  end
  if #stopped > 0 then kill_runs(stopped) end
end

---------------------------------------------------------------- Régions onglet
local function stop_in(lib)
  with_proj(lib, function() reaper.OnStopButton() end)
end

local function stop_ext(ids, dur)
  local only
  if ids then
    only = {}
    for _, id in ipairs(ids) do only[id] = true end
  end
  for id, r in pairs(ext_runs) do
    if (not only or only[id]) and not r.stopping then
      r.stopping = {t0 = reaper.time_precise(), dur = math.max(0.01, dur or 1)}
    end
  end
end

local function process_ext(now)
  if next(ext_runs) == nil then return end
  for id, r in pairs(ext_runs) do
    local playing = (math.floor(reaper.GetPlayStateEx(r.proj)) & 1) ~= 0
    if not playing then
      if now - r.t0 > 0.8 then
        reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0)
        if not r.seen then status = "La lecture n'a pas démarré dans l'onglet source." end
        ext_runs[id] = nil
      end
    else
      r.seen = true
      if r.stopping then
        local p = (now - r.stopping.t0) / r.stopping.dur
        if p >= 1 then
          stop_in(r.proj)
          reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0)
          ext_runs[id] = nil
        else
          reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0 * (1-p)^2)
        end
      elseif reaper.GetPlayPositionEx(r.proj) >= r.reg_end then
        stop_in(r.proj)
        reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0)
        ext_runs[id] = nil
      elseif r.fadein > 0 and not r.fade_done then
        local p = (now - r.t0) / r.fadein
        if p >= 1 then
          reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0)
          r.fade_done = true
        else
          reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0 * p)
        end
      end
    end
  end
end

local function fire_cue_inplace(a, lib, reg)
  local master = reaper.GetMasterTrack(lib)
  local old = ext_runs[a.id]
  local v0 = old and old.v0 or reaper.GetMediaTrackInfo_Value(master, "D_VOL")
  local fadein = a.fadein or 0
  with_proj(lib, function()
    if (math.floor(reaper.GetPlayStateEx(lib)) & 1) ~= 0 then reaper.OnStopButton() end
    reaper.SetEditCurPos2(lib, reg.s, false, false)
    if fadein > 0 then reaper.SetMediaTrackInfo_Value(master, "D_VOL", 0) end
    reaper.OnPlayButton()
  end)
  ext_runs[a.id] = {
    proj = lib, master = master, reg_end = reg.e, v0 = v0,
    t0 = reaper.time_precise(), fadein = fadein
  }
  local pre = ""
  if a.has_preset and a.snap then
    local ntr = apply_snap(a, a.link_time and fadein or 0, 0)
    pre = string.format(" + preset (%d piste(s))", ntr)
  end
  status = string.format("CUE \"%s\" : région \"%s\" jouée dans son onglet%s", a.name, reg.name, pre)
end

---------------------------------------------------------------- CUE
local function release_holds()
  -- Un nouveau déclenchement libère tout de suite les fondus terminés (en attente
  -- de HOLD). Les jobs de fondu ne stockent plus de volume de piste (v0) : on
  -- restaure le volume des items conservés, sans jamais toucher aux faders.
  for key, j in pairs(fades) do
    if j.done then
      for _, saved in ipairs(j.items or {}) do
        for k = 0, reaper.CountMediaItems(PROJ)-1 do
          local it = reaper.GetMediaItem(PROJ, k)
          local _, guid = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
          if guid == saved.guid then
            reaper.SetMediaItemInfo_Value(it, "D_VOL", saved.vol)
            break
          end
        end
      end
      if j.tr and j.v0 and reaper.ValidatePtr2(PROJ, j.tr, "MediaTrack*") then
        reaper.SetMediaTrackInfo_Value(j.tr, "D_VOL", j.v0) -- anciens jobs seulement
      end
      fades[key] = nil
    end
  end
end

local function stop_previous(id, t_start, fade)
  local t_end = t_start + math.max(0.005, fade or 0.03)
  local latest = t_start
  for i = reaper.CountMediaItems(PROJ)-1, 0, -1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
    local _, ka = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_keepalive", "", false)
    if mark == id and ka == "1" then
      reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
    elseif mark == id then
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if pos >= t_start then
        reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
      elseif pos + len > t_start then
        local new_end = math.min(pos + len, t_end)
        reaper.SetMediaItemInfo_Value(it, "D_LENGTH", new_end - pos)
        reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", new_end - t_start)
        if new_end > latest then latest = new_end end
      end
    end
  end
  return latest
end

local function fire_cue(a)
  release_holds()
  -- La boucle est gérée par la cue (Li/Lo) : on coupe le Repeat de REAPER pour
  -- éviter qu'il ne reboucle la lecture (conflit avec Devamp / suite jusqu'à OUT).
  if reaper.GetSetRepeat then reaper.GetSetRepeat(0) end
  local from_file = (a.src == "file")
  local lib, reg

  if from_file then
    if not a.file or a.file == "" then
      status = "Cue \""..a.name.."\" : aucun fichier choisi."
      return
    end
    if not a.track or not find_track(a.track) then
      a.track = default_track_guid()
      if not a.track then
        status = "Cue \""..a.name.."\" : le projet ne contient aucune piste. Ajoute une piste puis réessaie."
        return
      end
      save()
    end
  else
    lib = find_project(a.projfn)
    if not lib then
      status = "Cue \""..a.name.."\" : projet source non ouvert."
      return
    end
    for _, r in ipairs(get_regions(lib)) do
      if r.idx == a.region then reg = r end
    end
    if not reg then
      status = "Cue \""..a.name.."\" : région introuvable."
      return
    end
    if lib ~= PROJ and not a.copy then
      fire_cue_inplace(a, lib, reg)
      return
    end
  end

  local dest = a.track and find_track(a.track)
  if a.track and not dest then
    status = "Cue \""..a.name.."\" : piste introuvable."
    return
  end

  local playing = is_playing()
  -- Position cible initiale (recalée juste avant la création de l'item : si le
  -- traitement a pris du temps, la playhead peut avoir dépassé ce point et la
  -- nouvelle cue partirait alors au milieu du fichier).
  local target = stop_previous(tostring(a.id), now_pos() + margin/1000, ANTICLICK)
  runs[a.id] = nil
  local fadein = a.fadein or 0
  local count, missing, found = 0, nil, 0
  local used, notes = {}, {}

  local function mark(new)
    reaper.GetSetMediaItemInfo_String(new, "P_EXT:cuelist", "1", true)
    reaper.GetSetMediaItemInfo_String(new, "P_EXT:cuelist_id", tostring(a.id), true)
  end
  local function use_track(tr, nch)
    used[reaper.GetTrackGUID(tr)] = tr
    local n = adjust_channels(tr, nch)
    if n then notes[#notes+1] = track_name(tr).." portée à "..n.." canaux" end
  end

  reaper.PreventUIRefresh(1)

  if from_file then
    local probe = reaper.PCM_Source_CreateFromFile(a.file)
    if probe then
      local full = reaper.GetMediaSourceLength(probe)
      local nch  = reaper.GetMediaSourceNumChannels(probe)
      reaper.PCM_Source_Destroy(probe)
      -- Chaque déclenchement repart du point d'entrée enregistré (0 par défaut),
      -- jamais de la position où le transport REAPER a été arrêté.
      local tin  = math.max(0, math.min(tonumber(a.inpt) or 0, full-0.05))
      local tout = math.max(tin+0.05, math.min(a.outpt or full, full))
      local li   = math.max(tin, math.min(tonumber(a.loop_in) or tin, tout - 0.01))
      local lo   = math.max(li + 0.01, math.min(tonumber(a.loop_out) or tout, tout))
      local env  = a.env
      use_track(dest, nch)
      local speed = math.max(0.01, math.min(16, tonumber(a.wave_speed) or 1))
      -- Recaler la position si la playhead a avancé pendant la préparation.
      do
        local now_t = now_pos() + margin/1000
        if now_t > target then
          target = stop_previous(tostring(a.id), now_t, ANTICLICK)
        end
      end
      -- Départ toujours depuis IN. Si boucle : premier segment IN→LO, puis cycles LI→LO.
      local first_src = tin
      local first_seg, phase, loop_on
      if a.loop then
        first_seg = math.max(0.01, lo - tin)
        phase = "intro"
        loop_on = true
      else
        first_seg = math.max(0.01, tout - tin)
        phase = "once"
        loop_on = false
      end
      local proj_seg = first_seg / speed
      local it = add_file_item(dest, a.file, target, first_src, first_seg, math.min(fadein, proj_seg), env_gain(env, first_src), a.id, a.markers)
      if it then
        local ntk = reaper.GetActiveTake(it)
        if ntk then reaper.SetMediaItemTakeInfo_Value(ntk, "D_STARTOFFS", first_src) end
        count = 1
        local lc = tonumber(a.loop_count)
        if lc and lc <= 0 then lc = nil end
        devamp_flags[a.id] = nil
        runs[a.id] = {
          t0 = target, tin = tin, li = li, lo = lo, tout = tout,
          seg = math.max(0.01, lo - li),
          speed = speed, proj_seg = proj_seg,
          loop = loop_on,
          loop_count = lc,
          loops_done = 0,
          phase = phase,
          next = target + proj_seg,
          dest_guid = a.track, file = a.file, env = env or {}, markers = a.markers or {},
          alive = true, paused = false, pause_src = nil, devamp = false,
          item = it, id = a.id
        }
      end
    end
  else
    local list, first = {}, math.huge
    for i = 0, reaper.CountMediaItems(lib)-1 do
      local it = reaper.GetMediaItem(lib, i)
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      if pos >= reg.s - 1e-6 and pos < reg.e then
        list[#list+1] = it
        if pos < first then first = pos end
      end
    end
    found = #list
    for _, it in ipairs(list) do
      local tk = reaper.GetActiveTake(it)
      if tk then
        local d = dest
        if not d then
          local src_tr = reaper.GetMediaItem_Track(it)
          if lib == PROJ then
            d = src_tr
          else
            local tname = track_name(src_tr)
            d = find_track_by_name(tname)
            if not d then
              d = create_track(tname)
              if d then notes[#notes+1] = "piste \""..tname.."\" créée"
              else missing = tname end
            end
          end
        end
        if d then
          local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
          local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
          local new, ntk
          if reaper.TakeIsMIDI(tk) then
            -- Crée un véritable item MIDI indépendant dans le projet cible,
            -- puis copie le flux MIDI complet (notes, CC, événements texte, etc.).
            new = reaper.CreateNewMIDIItemInProj(d, target + (pos - reg.s), target + (pos - reg.s) + len, false)
            ntk = new and reaper.GetActiveTake(new)
            if ntk and reaper.MIDI_GetAllEvts and reaper.MIDI_SetAllEvts then
              local ok, events = reaper.MIDI_GetAllEvts(tk, "")
              if ok and events then reaper.MIDI_SetAllEvts(ntk, events) end
            end
            if new then
              for _, p in ipairs(item_props) do
                reaper.SetMediaItemInfo_Value(new, p, reaper.GetMediaItemInfo_Value(it, p))
              end
              if ntk then
                for _, p in ipairs(take_props) do
                  reaper.SetMediaItemTakeInfo_Value(ntk, p, reaper.GetMediaItemTakeInfo_Value(tk, p))
                end
                copy_take_markers(tk, ntk)
              end
            end
          else
            local file = reaper.GetMediaSourceFileName(reaper.GetMediaItemTake_Source(tk), "")
            new = reaper.AddMediaItemToTrack(d)
            ntk = reaper.AddTakeToMediaItem(new)
            local src = reaper.PCM_Source_CreateFromFile(file)
            if src then reaper.SetMediaItemTake_Source(ntk, src) end
            for _, p in ipairs(item_props) do
              reaper.SetMediaItemInfo_Value(new, p, reaper.GetMediaItemInfo_Value(it, p))
            end
            for _, p in ipairs(take_props) do
              reaper.SetMediaItemTakeInfo_Value(ntk, p, reaper.GetMediaItemTakeInfo_Value(tk, p))
            end
            copy_take_markers(tk, ntk)
            reaper.SetMediaItemInfo_Value(new, "D_POSITION", target + (pos - reg.s))
            if fadein > 0 and pos - first < 1e-6 then
              reaper.SetMediaItemInfo_Value(new, "D_FADEINLEN", math.min(fadein, len))
            end
          end
          if new and ntk then
            mark(new)
            reaper.UpdateItemInProject(new)
            if not reaper.TakeIsMIDI(ntk) then
              use_track(d, reaper.GetMediaSourceNumChannels(reaper.GetMediaItemTake_Source(ntk)))
            end
            count = count + 1
          end
        end
      end
    end
  end

  if count > 0 and prefs.exclusive_track ~= false then
    -- Fondu de l'ancienne cue = fade-in de la nouvelle (comportement voulu).
    replace_on_tracks(used, a.id, target, fadein)
  end
  reaper.PreventUIRefresh(-1)
  reaper.UpdateArrange()

  if count == 0 then
    status = missing and ("Cue \""..a.name.."\" : impossible de créer la piste \""..missing.."\".")
                     or (from_file and ("Cue \""..a.name.."\" : fichier illisible.")
                       or string.format("Cue \"%s\" : aucun item exploitable.", a.name))
    return
  end
  if not playing then play_main() end
  cue_session = true

  local pre = ""
  if a.has_preset and a.snap then
    local ntr = apply_snap(a, a.link_time and fadein or 0, math.max(0, target - now_pos()))
    pre = string.format(" + preset (%d piste(s))", ntr)
  end
  status = string.format("CUE \"%s\" : %d item(s) à %.2f s%s%s",
    a.name, count, target, pre,
    #notes > 0 and (" | "..table.concat(notes, ", ")) or "")
end

---------------------------------------------------------------- STOP
local function cleanup_track(tr, keep)
  -- keep = true  → Delete on stop décoché : ne pas toucher aux items
  --                (ils restent entiers sur la timeline).
  -- keep = false → Delete on stop coché : tout supprimer sur la piste.
  if keep then return end
  for _, t in ipairs(tracks_of(tr)) do
    for i = reaper.CountTrackMediaItems(t)-1, 0, -1 do
      local it = reaper.GetTrackMediaItem(t, i)
      local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
      if mark == "1" then
        reaper.DeleteTrackMediaItem(t, it)
      end
    end
  end
  reaper.UpdateArrange()
end

-- Supprime les items ActionList du projet.
-- cue_ids optionnel : table {["12"]=true, ...} pour ne cibler que ces IDs.
delete_cuelist_items = function(cue_ids)
  local n = 0
  for i = reaper.CountMediaItems(PROJ) - 1, 0, -1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
    if mark == "1" then
      local ok = true
      if cue_ids then
        local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
        ok = cid ~= "" and cue_ids[cid] == true
      end
      if ok then
        reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
        n = n + 1
      end
    end
  end
  if n > 0 then reaper.UpdateArrange() end
  return n
end

delete_all_cuelist_items = function()
  return delete_cuelist_items(nil)
end

local function stop_all(dur)
  dur = dur or stop_fade
  kill_runs(nil)
  stop_ext(nil, dur)
  local p = now_pos()
  local seen, n = {}, 0
  local finished_deleted = 0

  -- 1) Items déjà terminés (entièrement avant la playhead) : suppression immédiate
  --    si Delete on stop est actif.
  if prefs.delete_on_stop == true then
    for i = reaper.CountMediaItems(PROJ) - 1, 0, -1 do
      local it = reaper.GetMediaItem(PROJ, i)
      local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
      if mark == "1" then
        local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
        local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
        if pos + len <= p + 1e-6 then
          reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
          finished_deleted = finished_deleted + 1
        end
      end
    end
  end

  -- 2) Items encore en cours / futurs : fondu puis nettoyage.
  for i = 0, reaper.CountMediaItems(PROJ)-1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
    if mark == "1" then
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if pos + len > p then
        local tr = reaper.GetMediaItem_Track(it)
        local g = reaper.GetTrackGUID(tr)
        if not seen[g] then
          seen[g] = true
          if not fades[g] then
            n = n + 1
            local items = {}
            for j = 0, reaper.CountTrackMediaItems(tr)-1 do
              local cue_item = reaper.GetTrackMediaItem(tr, j)
              local _, cue_mark = reaper.GetSetMediaItemInfo_String(cue_item, "P_EXT:cuelist", "", false)
              local ipos = reaper.GetMediaItemInfo_Value(cue_item, "D_POSITION")
              local ilen = reaper.GetMediaItemInfo_Value(cue_item, "D_LENGTH")
              if cue_mark == "1" and ipos + ilen > p then
                local _, iguid = reaper.GetSetMediaItemInfo_String(cue_item, "GUID", "", false)
                items[#items+1] = {guid=iguid, vol=reaper.GetMediaItemInfo_Value(cue_item, "D_VOL")}
              end
            end
            fades[g] = {
              tr = tr, items = items, t0 = reaper.time_precise(),
              dur = math.max(0.01, dur), keep = prefs.delete_on_stop ~= true
            }
          end
        end
      end
    end
  end

  -- 3) Filet de sécurité : après le fondu, tout item ActionList restant disparaît.
  if prefs.delete_on_stop == true then
    del_jobs[#del_jobs + 1] = {
      at = reaper.time_precise() + math.max(0.01, dur) + 0.15,
      all_cuelist = true
    }
  end
  if n > 0 then
    status = string.format("STOP : fondu %.1f s (%d piste(s))%s",
      dur, n, prefs.delete_on_stop and " → suppression des items après fondu" or "")
  elseif finished_deleted > 0 then
    status = string.format("STOP : %d item(s) ActionList déjà terminé(s) supprimé(s).", finished_deleted)
  else
    status = prefs.delete_on_stop
      and "STOP : rien en cours (nettoyage programmé si items restants)."
      or "STOP : rien en cours."
  end
  if finished_deleted > 0 or n > 0 then reaper.UpdateArrange() end
end

local function stop_targets(ids, dur)
  kill_runs(ids)
  stop_ext(ids, dur)
  local set = {}
  for _, id in ipairs(ids) do set[tostring(id)] = true end
  local t_start = now_pos() + margin/1000
  local t_end = t_start + dur
  local n, affected = 0, {}
  for i = reaper.CountMediaItems(PROJ)-1, 0, -1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
    if set[mark] then
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if pos + len > t_start then
        n = n + 1
        if prefs.delete_on_stop == true then
          -- Option coché : on coupe / programme la suppression.
          if pos >= t_start then
            reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
          else
            local new_end = math.min(pos + len, t_end)
            reaper.SetMediaItemInfo_Value(it, "D_LENGTH", new_end - pos)
            reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", new_end - t_start)
            local _, g = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
            affected[g] = true
          end
        else
          -- Option décoché : fondu volume seulement, item laissé intact sur la timeline.
          reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN",
            math.max(reaper.GetMediaItemInfo_Value(it, "D_FADEOUTLEN"),
              math.min(len, math.max(0, pos + len - t_start), dur)))
        end
      end
    end
  end
  if prefs.delete_on_stop == true then
    local id_set = {}
    for id in pairs(set) do id_set[id] = true end
    del_jobs[#del_jobs + 1] = {
      at = reaper.time_precise() + margin/1000 + dur + 0.25,
      cue_ids = id_set,
      guids = next(affected) and affected or nil
    }
  end
  reaper.UpdateArrange()
  status = string.format("STOP ciblé : fade de %.1f s, %d item(s)%s",
    dur, n, prefs.delete_on_stop == true and " → suppression" or " (items conservés)")
end

function X.apply_linked_preset(a, dur)
  if a.has_preset and a.snap then
    local ntr = apply_snap(a, a.link_time and (dur or 0) or 0, 0)
    status = (status or "") .. string.format(" + preset (%d piste(s))", ntr)
  end
end

local function fire_stop(a)
  local dur = a.dur or 1
  -- Le champ Q1,Q8 est la source de vérité lorsqu'il est présent.
  if type(a.targets_text) == "string" then
    local parsed, seen, invalid = {}, {}, false
    for token in (a.targets_text .. ","):gmatch("(.-),") do
      token = token:match("^%s*(.-)%s*$")
      if token ~= "" then
        local digits = token:match("^[Qq]?(%d+)$")
        if digits then
          local id = tonumber(digits)
          if not seen[id] then parsed[#parsed+1] = id; seen[id] = true end
        else invalid = true end
      end
    end
    if not invalid then a.targets = (#parsed > 0) and parsed or nil end
  end
  local targeted = a.targets and #a.targets > 0
  if a.id then
    stop_until[a.id] = reaper.time_precise() + dur + 0.2 + (targeted and margin/1000 or 0)
  end
  if targeted then stop_targets(a.targets, dur) else stop_all(dur) end
  X.apply_linked_preset(a, dur)
  -- Arrêt du transport = option "Arrêter la lecture…".
  -- Après le fondu seulement, sinon ESC coupe le fade net.
  if prefs.auto_stop then
    del_jobs[#del_jobs + 1] = {
      at = reaper.time_precise() + math.max(0.01, dur) + 0.05,
      stop_transport = true
    }
  end
end

function X.target_run_ids(a)
  local ids = resolve_targets(a)
  if ids then return ids end
  local all = {}
  for id in pairs(runs) do all[#all+1] = id end
  return all
end

local function fire_pause(a)
  local fade = math.max(0, tonumber(a.dur) or 0)
  local n = 0
  for _, id in ipairs(X.target_run_ids(a)) do
    if a.unpause == true then
      if resume_run(id, fade) then n = n + 1 end
    else
      if pause_run(id, fade) then n = n + 1 end
    end
  end
  status = string.format("%s : %d cue(s) concernée(s)%s.", a.unpause == true and "UNPAUSE" or "PAUSE", n,
    fade > 0 and string.format(", fade %.1f s", fade) or "")
  if a.id then stop_until[a.id] = nil end
  X.apply_linked_preset(a, fade)
end

local function fire_devamp(a)
  local n = 0
  for _, id in ipairs(X.target_run_ids(a)) do
    if devamp_run(id) then n = n + 1 end
  end
  status = string.format("DEVAMP : %d cue(s) armée(s).", n)
  X.apply_linked_preset(a, 0)
end

---------------------------------------------------------------- Nettoyage
local function clear_copies()
  runs = {}
  local n = 0
  for i = reaper.CountMediaItems(PROJ)-1, 0, -1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
    if mark == "1" then
      reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
      n = n + 1
    end
  end
  reaper.UpdateArrange()
  status = n.." copie(s) de cue supprimée(s)."
end

---------------------------------------------------------------- PRESET
local function capture(tr)
  local p = {
    vol = reaper.GetMediaTrackInfo_Value(tr, "D_VOL"),
    pan = reaper.GetMediaTrackInfo_Value(tr, "D_PAN"),
    fx = {}
  }
  for i = 0, reaper.TrackFX_GetCount(tr)-1 do
    local _, name = reaper.TrackFX_GetFXName(tr, i, "")
    local f = {name=name, enabled=reaper.TrackFX_GetEnabled(tr, i), params={}, use=true}
    for k = 0, reaper.TrackFX_GetNumParams(tr, i)-1 do
      local _, pn = reaper.TrackFX_GetParamName(tr, i, k, "")
      if pn ~= "Bypass" and pn ~= "Delta" then
        f.params[k+1] = reaper.TrackFX_GetParamNormalized(tr, i, k)
      end
    end
    p.fx[#p.fx+1] = f
  end
  return p
end

local function apply_steps(steps, p)
  for _, s in ipairs(steps) do
    if s.k == "vol" then
      reaper.SetMediaTrackInfo_Value(s.tr, "D_VOL", lerp_db(s.from, s.to, p))
    elseif s.k == "pan" then
      reaper.SetMediaTrackInfo_Value(s.tr, "D_PAN", s.from + (s.to - s.from)*p)
    else
      reaper.TrackFX_SetParamNormalized(s.tr, s.fx, s.p, s.from + (s.to - s.from)*p)
    end
  end
end

local function ensure_snap(a)
  if not a.snap and a.data and a.track then
    a.snap = {order={a.track}, tracks={[a.track]=a.data}}
    a.data = nil
    save()
  end
end

local function snap_add(snap, tr)
  local g = reaper.GetTrackGUID(tr)
  local st = capture(tr)
  st.name = track_name(tr)
  st.include = true
  snap.order[#snap.order+1] = g
  snap.tracks[g] = st
end

local function current_value(s)
  if s.k == "vol" then return reaper.GetMediaTrackInfo_Value(s.tr, "D_VOL")
  elseif s.k == "pan" then return reaper.GetMediaTrackInfo_Value(s.tr, "D_PAN")
  else return reaper.TrackFX_GetParamNormalized(s.tr, s.fx, s.p) end
end

local function start_morph(m)
  m.started = true
  local keys, kept = {}, {}
  for _, s in ipairs(m.steps) do
    s.from = current_value(s)
    keys[s.key] = true
    if math.abs(s.from - s.to) > 1e-6 then kept[#kept+1] = s end
  end
  m.steps = kept
  for _, o in ipairs(morphs) do
    if o ~= m and o.started then
      local rest = {}
      for _, s in ipairs(o.steps) do
        if not keys[s.key] then rest[#rest+1] = s end
      end
      o.steps = rest
    end
  end
  for _, e in ipairs(m.enables or {}) do
    reaper.TrackFX_SetEnabled(e.tr, e.fx, e.val)
  end
end

apply_snap = function(a, dur, delay)
  ensure_snap(a)
  local use = a.use or {vol=true, pan=true, fxen=true, fxpar=true}
  local steps, enables, warns, ntr = {}, {}, {}, 0
  if not a.snap then return 0, warns end
  for _, g in ipairs(a.snap.order) do
    local d = a.snap.tracks[g]
    local tr = find_track(g)
    if d and d.include ~= false then
      if not tr then
        warns[#warns+1] = (d.name or "?").." introuvable"
      else
        ntr = ntr + 1
        if use.vol and d.vol then
          steps[#steps+1] = {k="vol", tr=tr, to=d.vol, key=g.."|vol"}
        end
        if use.pan and d.pan then
          steps[#steps+1] = {k="pan", tr=tr, to=d.pan, key=g.."|pan"}
        end
        for i, f in ipairs(d.fx or {}) do
          if f.use then
            local idx = i-1
            local _, nm = reaper.TrackFX_GetFXName(tr, idx, "")
            if nm == f.name then
              if use.fxen then
                enables[#enables+1] = {tr=tr, fx=idx, val=f.enabled}
              end
              if use.fxpar then
                for pk, val in pairs(f.params) do
                  steps[#steps+1] = {
                    k="par", tr=tr, fx=idx, p=pk-1, to=val,
                    key = g.."|"..idx.."|"..(pk-1)
                  }
                end
              end
            else
              warns[#warns+1] = track_name(tr).." : effet "..i.." différent"
            end
          end
        end
      end
    end
  end
  dur, delay = dur or 0, delay or 0
  local m = {
    steps = steps, enables = enables,
    t0 = reaper.time_precise() + math.max(0, delay),
    dur = math.max(dur, 0.001)
  }
  if dur <= 0 and delay <= 0 then
    start_morph(m)
    apply_steps(m.steps, 1)
  else
    morphs[#morphs+1] = m
  end
  return ntr, warns
end

local function fire_preset(a)
  ensure_snap(a)
  if not a.snap or #a.snap.order == 0 then
    status = "PRESET \""..a.name.."\" : rien de capturé."
    return
  end
  local ntr, warns = apply_snap(a, a.dur or 0, 0)
  status = string.format("PRESET \"%s\" : %d piste(s)", a.name, ntr)
    .. (#warns > 0 and (" - "..table.concat(warns, ", ")) or "")
end

---------------------------------------------------------------- OSC / MIDI
local function send_osc(port_def, address, args)
  if not has_socket then
    status = "OSC : Mavriq Lua Sockets 1.2 absent ou non chargeable."
    return
  end
  if not port_def or not port_def.ip or not port_def.port then
    status = "OSC : port invalide."
    return
  end
  local ok, udp = pcall(socket.udp)
  if not ok or not udp then
    status = "OSC : impossible de créer le socket UDP."
    return
  end
  udp:settimeout(0)
  local packet = osc_encode(address or "/", args)
  local sent, err = udp:sendto(packet, port_def.ip, port_def.port)
  udp:close()
  if sent then
    local argstr = ""
    if type(args) == "table" then
      for _, v in ipairs(args) do argstr = argstr.." "..tostring(v) end
    end
    status = string.format("OSC → %s (%s:%d)  %s%s",
      port_def.name or "?", port_def.ip, port_def.port, address or "/", argstr)
  else
    status = "OSC : échec d'envoi ("..tostring(err)..")"
  end
end

local function fire_osc(a)
  local port_def
  for _, p in ipairs(prefs.ports or {}) do
    if p.name == a.port_name then port_def = p break end
  end
  if not port_def then
    status = "OSC \""..(a.name or "").."\" : port \""..(a.port_name or "").."\" introuvable."
    return
  end
  send_osc(port_def, a.address or "/", a.args)
end

-- Configure la piste relais : Virtual Keyboard + arm + monitoring.
local function ensure_track_midi_vkb(tr)
  if not tr then return false end
  local recinput = math.floor(reaper.GetMediaTrackInfo_Value(tr, "I_RECINPUT") or 0)
  if recinput ~= MIDI_VKB_RECINPUT then
    reaper.SetMediaTrackInfo_Value(tr, "I_RECINPUT", MIDI_VKB_RECINPUT)
  end
  if reaper.GetMediaTrackInfo_Value(tr, "I_RECARM") < 0.5 then
    reaper.SetMediaTrackInfo_Value(tr, "I_RECARM", 1)
  end
  local mon = reaper.GetMediaTrackInfo_Value(tr, "I_RECMON") or 0
  if mon < 0.5 then
    reaper.SetMediaTrackInfo_Value(tr, "I_RECMON", 1)
  end
  return true
end

local function ensure_midi_relay_track()
  local tr = find_track_by_name(MIDI_RELAY_NAME)
  if not tr then
    tr = create_track(MIDI_RELAY_NAME)
  end
  if tr then ensure_track_midi_vkb(tr) end
  return tr
end

-- Rebuild des sends MIDI-only depuis la relais vers chaque destination connue.
local function rebuild_midi_relay_sends(relay)
  if not relay then return end
  for i = reaper.GetTrackNumSends(relay, 0) - 1, 0, -1 do
    reaper.RemoveTrackSend(relay, 0, i)
  end
  for guid, dest in pairs(midi_relay_dests) do
    if dest and reaper.ValidatePtr2(PROJ, dest, "MediaTrack*") then
      local idx = reaper.CreateTrackSend(relay, dest)
      if idx and idx >= 0 then
        reaper.SetTrackSendInfo_Value(relay, 0, idx, "I_SRCCHAN", -1) -- pas d'audio
        reaper.SetTrackSendInfo_Value(relay, 0, idx, "I_MIDIFLAGS", 0) -- tout le MIDI
      end
    else
      midi_relay_dests[guid] = nil
    end
  end
end

local function ensure_midi_relay_to(dest)
  local relay = ensure_midi_relay_track()
  if not relay or not dest then return nil end
  local guid = reaper.GetTrackGUID(dest)
  if not midi_relay_dests[guid] then
    midi_relay_dests[guid] = dest
    rebuild_midi_relay_sends(relay)
  else
    midi_relay_dests[guid] = dest
    -- S'assurer que la relais est toujours armée même si le send existe déjà.
    ensure_track_midi_vkb(relay)
  end
  return relay
end

local function fire_midi(a)
  local tr = a.track and find_track(a.track)
  if not tr then
    status = 'MIDI "'..(a.name or "")..'" : piste cible introuvable.'
    return
  end
  if type(reaper.StuffMIDIMessage) ~= "function" then
    status = "MIDI : StuffMIDIMessage indisponible dans cette version de REAPER."
    return
  end

  local relay = ensure_midi_relay_to(tr)
  if not relay then
    status = 'MIDI "'..(a.name or "")..'" : impossible de créer la piste relais « '..MIDI_RELAY_NAME..' ».'
    return
  end

  local ch = math.max(0, math.min(15, (a.channel or 1) - 1))
  local typ = a.midi_type or "note"
  local detail

  if typ == "note" then
    local note = math.max(0, math.min(127, a.note or 60))
    local vel  = math.max(0, math.min(127, a.velocity or 100))
    reaper.StuffMIDIMessage(0, 0x90 + ch, note, vel)
    if vel > 0 then
      midi_note_offs[#midi_note_offs + 1] = {
        t = reaper.time_precise() + (MIDI_NOTE_DURATION_MS / 1000),
        status = 0x80 + ch,
        note = note,
      }
    end
    detail = string.format("note %d vel %d, durée %d ms", note, vel, MIDI_NOTE_DURATION_MS)
  elseif typ == "cc" then
    local cc  = math.max(0, math.min(127, a.cc or 1))
    local val = math.max(0, math.min(127, a.value or 0))
    reaper.StuffMIDIMessage(0, 0xB0 + ch, cc, val)
    detail = string.format("CC %d = %d", cc, val)
  elseif typ == "pc" then
    local prog = math.max(0, math.min(127, a.program or 0))
    reaper.StuffMIDIMessage(0, 0xC0 + ch, prog, 0)
    detail = string.format("Program %d", prog)
  else
    status = "MIDI : type inconnu"
    return
  end

  status = string.format('MIDI "%s" → « %s » via relais « %s » (%s, canal %d)',
    a.name or "", track_name(tr), MIDI_RELAY_NAME, detail, ch + 1)
end

local function poll_midi_note_offs()
  if #midi_note_offs == 0 then return end
  local now = reaper.time_precise()
  local remain = {}
  for _, n in ipairs(midi_note_offs) do
    if now >= n.t then
      reaper.StuffMIDIMessage(0, n.status, n.note, 0)
    else
      remain[#remain + 1] = n
    end
  end
  midi_note_offs = remain
end

---------------------------------------------------------------- Take markers Qxx
local fired_markers = {}
local last_marker_scan = 0
local last_project_playpos = {}

local function parse_q_ids(name)
  local ids = {}
  if not name then return ids end
  for token in name:gmatch("[Qq]%s*([%d%.]+)") do
    local n = tonumber(token)
    if n then ids[#ids+1] = n end
  end
  return ids
end

local function clear_fired_for_project(project_key)
  local prefix = project_key .. "|"
  for key in pairs(fired_markers) do
    if key:sub(1, #prefix) == prefix then fired_markers[key] = nil end
  end
end

local function action_for_qid(qid)
  return actions_by_id[qid] or actions_by_id[tostring(qid)] or actions_by_id[tonumber(qid)]
end

local function fire_qids_once(project_key, guid, abspos, qids)
  for _, qid in ipairs(qids or {}) do
    local key = project_key .. "|" .. tostring(guid) .. "|Q|" .. tostring(qid) .. "|" .. string.format("%.4f", abspos)
    if not fired_markers[key] then
      local act = action_for_qid(qid)
      fired_markers[key] = true
      if act then
        fire(act)
      else
        status = string.format("Marqueur Q%s détecté, mais aucun cue avec l'ID %s n'existe dans cette ActionList.", tostring(qid), tostring(qid))
      end
    end
  end
end

local function process_take_markers(now)
  if now - last_marker_scan < 0.02 then return end
  last_marker_scan = now
  local playing_projects = {}
  local idx = 0
  while idx < 128 do
    local proj = reaper.EnumProjects(idx, "")
    if not proj then break end
    if (math.floor(reaper.GetPlayStateEx(proj)) & 1) ~= 0 then
      playing_projects[#playing_projects+1] = {proj = proj, key = tostring(proj)}
    end
    idx = idx + 1
  end
  if #playing_projects == 0 then
    fired_markers = {}
    last_project_playpos = {}
    return
  end
  local look_ahead = math.max(0.05, margin / 1000 + 0.05)
  for _, entry in ipairs(playing_projects) do
    local proj, project_key = entry.proj, entry.key
    local p = reaper.GetPlayPosition2Ex(proj)
    local prev = last_project_playpos[project_key]
    if prev and p < prev - 0.20 then
      clear_fired_for_project(project_key)
      prev = nil
    end
    local lower_bound = prev and (prev - 0.025) or (p - 0.15)
    for i = 0, reaper.CountMediaItems(proj)-1 do
      local it = reaper.GetMediaItem(proj, i)
      -- Sécurité : un projet peut changer pendant l'énumération (fermeture/ouverture,
      -- suppression d'item). Ne jamais appeler GetMediaItemInfo_Value avec nil.
      if it then
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if p + look_ahead >= pos and p < pos + len + 0.1 then
        local tk = reaper.GetActiveTake(it)
        if tk then
          local _, guid = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
          local rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE")
          if not rate or rate <= 0 then rate = 1 end
          local startoffs = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS") or 0
          local nmark = reaper.GetNumTakeMarkers(tk)
          for m = 0, nmark-1 do
            local mpos, mname = reaper.GetTakeMarker(tk, m)
            if mpos and mpos >= 0 and mname and mname ~= "" then
              local qids = parse_q_ids(mname)
              if #qids > 0 then
                local rel = (mpos - startoffs) / rate
                local abs = pos + rel
                local valid_in_item = rel >= -0.02 and rel <= len + 0.02
                if valid_in_item and abs >= lower_bound and abs <= p + look_ahead then
                  fire_qids_once(project_key, guid, abs, qids)
                end
              end
            end
          end
        end
      end
      end -- if it then
    end
    last_project_playpos[project_key] = p
  end
end

---------------------------------------------------------------- Jobs
local function process_jobs()
  local now = reaper.time_precise()
  if play_check and now >= play_check then
    play_check = nil
    if not is_playing() then
      status = "Attention : la lecture n'a pas démarré."
    end
  end
  process_runs(now)
  process_ext(now)
  refresh_active(now)
  process_take_markers(now)
  -- Arrêt transport = option "Arrêter la lecture quand plus aucun média…".
  -- Delete on stop = suppression des items uniquement (indépendant).
  if prefs.auto_stop then
    if is_playing() then
      np_since = nil
      if cue_session and now - last_scan > 0.25 then
        last_scan = now
        local still_busy = auto_chain or (next(runs) ~= nil)
        if active_cue_items() or still_busy then
          idle_since = nil
        else
          idle_since = idle_since or now
          if now - idle_since >= 0.3 then
            if prefs.delete_on_stop == true then delete_all_cuelist_items() end
            stop_here() -- revient au point de départ de la session
            cue_session, idle_since = false, nil
            status = "Lecture arrêtée : plus aucun média."
          end
        end
      end
    else
      np_since = np_since or now
      if now - (np_since or now) > 1 then cue_session, idle_since = false, nil end
    end
  end
  -- Delete on stop : nettoyer les items restants une fois le transport arrêté,
  -- sans décider d'interrompre ou non la lecture.
  if not is_playing() then
    np_since = np_since or now
  else
    np_since = nil
  end
  if prefs.delete_on_stop == true and cue_session and not is_playing() then
    if np_since and (now - np_since) > 0.5 then
      local n = delete_all_cuelist_items()
      local pos = session_origin or reaper.GetCursorPositionEx(PROJ)
      reaper.SetEditCurPos2(PROJ, pos, true, false)
      cue_session = false
      if n > 0 then
        status = string.format("Nettoyage : %d item(s) supprimé(s).", n)
      end
    end
  end
  for i = #del_jobs, 1, -1 do
    local j = del_jobs[i]
    if now >= j.at then
      if j.stop_transport then
        if prefs.auto_stop then
          stop_here()
          cue_session = false
        end
      elseif prefs.delete_on_stop == true then
        -- Ne supprimer que si l'option est ENCORE active au moment de l'exécution.
        if j.all_cuelist then
          delete_all_cuelist_items()
        else
          for k = reaper.CountMediaItems(PROJ) - 1, 0, -1 do
            local it = reaper.GetMediaItem(PROJ, k)
            local delete = false
            if j.guids then
              local _, g = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
              if j.guids[g] then delete = true end
            end
            if not delete and j.cue_ids then
              local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
              if cid ~= "" and j.cue_ids[cid] then delete = true end
            end
            if delete then
              reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
            end
          end
          reaper.UpdateArrange()
        end
      end
      table.remove(del_jobs, i)
    end
  end
  for key, j in pairs(fades) do
    if j.done then
      if now >= j.done + HOLD then
        -- Restore original item volumes for retained cue items; never touch track faders.
        for _, saved in ipairs(j.items or {}) do
          for k = 0, reaper.CountMediaItems(PROJ)-1 do
            local it = reaper.GetMediaItem(PROJ, k)
            local _, guid = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
            if guid == saved.guid then
              reaper.SetMediaItemInfo_Value(it, "D_VOL", saved.vol)
              break
            end
          end
        end
        fades[key] = nil
      end
    else
      local p = (now - j.t0) / j.dur
      if p >= 1 then
        cleanup_track(j.tr, j.keep)
        j.done = now
      else
        local gain = (1-p)^2
        for _, saved in ipairs(j.items or {}) do
          for k = 0, reaper.CountMediaItems(PROJ)-1 do
            local it = reaper.GetMediaItem(PROJ, k)
            local _, guid = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
            if guid == saved.guid then
              reaper.SetMediaItemInfo_Value(it, "D_VOL", saved.vol * gain)
              break
            end
          end
        end
      end
    end
  end
  for i = #morphs, 1, -1 do
    local m = morphs[i]
    if now >= m.t0 then
      if not m.started then start_morph(m) end
      local p = (now - m.t0) / m.dur
      apply_steps(m.steps, math.min(1, p))
      if p >= 1 or #m.steps == 0 then table.remove(morphs, i) end
    end
  end
end

---------------------------------------------------------------- Fire
fire = function(a, from_auto_chain)
  if not a then return end
  -- Toute action déclenchée manuellement remplace le compte à rebours précédent.
  if not from_auto_chain then auto_chain = nil end
  if a.type == "cue"    then fire_cue(a)
  elseif a.type == "preset" then fire_preset(a)
  elseif a.type == "stop"   then fire_stop(a)
  elseif a.type == "pause"  then fire_pause(a)
  elseif a.type == "devamp" then fire_devamp(a)
  elseif a.type == "osc"    then fire_osc(a)
  elseif a.type == "midi"   then fire_midi(a)
  end
  -- AUTO et FOLLOW sont exclusifs. AUTO compte depuis le déclenchement ;
  -- FOLLOW attend la fin de l'action (durée audio / fondu STOP), puis DELAY.
  if a.auto == true or a.follow == true then
    local idx
    for i, candidate in ipairs(actions) do
      if candidate.id == a.id then idx = i; break end
    end
    if idx and actions[idx + 1] then
      local now = reaper.time_precise()
      local delay = math.max(0, tonumber(a.delay) or 0)
      local wait_until = now
      local wait_for_run = false
      if a.follow == true then
        if a.type == "cue" then
          local run = runs[a.id]
          if run then
            if run.loop then
              -- Une cue en boucle n'a pas de fin prévue : attendre son arrêt réel,
              -- puis commencer le DELAY.
              wait_for_run = true
              wait_until = now
            else
              -- FOLLOW : attendre la fin de l'item sur la timeline REAPER,
              -- puis ajouter DELAY. run.t0 est une position de projet (secondes),
              -- PAS une valeur de time_precise(); il faut convertir le temps restant
              -- en durée murale avant de créer deadline.
              -- FOLLOW suit la position réelle de la timeline : le traitement
              -- périodique recalculera l'attente si l'utilisateur fait un seek.
              wait_for_run = true
              wait_until = now
              
            end
          else
            -- Action sans lecture audio active : considérée terminée au déclenchement.
            wait_until = now
          end
        elseif a.type == "stop" then
          -- Pour STOP, la fin correspond à la fin de son fondu.
          wait_until = now + math.max(0, tonumber(a.dur) or tonumber(stop_fade) or 0)
        elseif a.type == "pause" then
          wait_until = now + math.max(0, tonumber(a.dur) or 0)
        else
          -- Preset / OSC / MIDI : action instantanée, puis DELAY.
          wait_until = now
        end
      end
      auto_chain = {
        source_id = a.id,
        next_id = actions[idx + 1].id,
        tab_index = active_tab,
        mode = a.follow == true and "follow" or "auto",
        wait_for_run = wait_for_run,
        follow_end = (a.follow == true and a.type == "cue" and runs[a.id] and not runs[a.id].loop)
          and ((tonumber(runs[a.id].t0) or now_pos()) + math.max(0, tonumber(runs[a.id].proj_seg or runs[a.id].seg) or 0)) or nil,
        delay_started = false,
        delay = delay,
        deadline = wait_until + delay,
      }
    end
  end
end

local function process_auto_chain()
  local chain = auto_chain
  if not chain then return end
  -- Ne pas lancer une cue d'un onglet devenu inactif ni un ID qui a été supprimé.
  if chain.tab_index ~= active_tab then auto_chain = nil; return end
  local now = reaper.time_precise()
  -- FOLLOW sur une cue audio attend la fin réelle prévue de sa lecture.
  if chain.mode == "follow" then
    local run = runs[chain.source_id]
    if chain.wait_for_run and run and run.loop then return end
    if chain.follow_end then
      -- Le délai ne démarre qu'une fois la tête de lecture arrivée à la fin.
      -- Un seek vers l'arrière annule le délai ; un seek vers l'avant le recalcule.
      local pos = now_pos()
      if pos < chain.follow_end then
        chain.delay_started = false
        chain.deadline = math.huge
        return
      end
      if not chain.delay_started then
        chain.delay_started = true
        chain.deadline = now + math.max(0, tonumber(chain.delay) or 0)
      end
    elseif chain.wait_for_run then
      if run then return end
      chain.wait_for_run = false
      chain.deadline = now + math.max(0, tonumber(chain.delay) or 0)
    end
  end
  if now < chain.deadline then return end
  auto_chain = nil
  for _, candidate in ipairs(actions) do
    if candidate.id == chain.next_id then
      fire(candidate, true)
      return
    end
  end
end

---------------------------------------------------------------- Interface utilitaires
local function mods_shift_multi()
  local shift, multi = false, false
  if reaper.ImGui_GetKeyMods then
    local m = reaper.ImGui_GetKeyMods(ctx)
    shift = (m & reaper.ImGui_Mod_Shift()) ~= 0
    if reaper.ImGui_Mod_Shortcut then
      multi = (m & reaper.ImGui_Mod_Shortcut()) ~= 0
    else
      multi = (m & reaper.ImGui_Mod_Ctrl()) ~= 0
      if reaper.ImGui_Mod_Super then
        multi = multi or (m & reaper.ImGui_Mod_Super()) ~= 0
      end
    end
  else
    shift = reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftShift())
        or reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightShift())
    multi = reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftCtrl())
        or reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightCtrl())
  end
  return shift, multi
end

local function pick_only(a, i)
  picked = {[a.id] = true}
  pick_anchor = i
  selected = a.id
end

local function pick_range(from_i, to_i)
  if from_i > to_i then from_i, to_i = to_i, from_i end
  picked = {}
  for i = from_i, to_i do
    picked[actions[i].id] = true
  end
end


-- Presse-papiers interne pour copier/couper plusieurs cues sélectionnées,
-- même si elles proviennent de plusieurs onglets.
local function collect_picked_actions()
  local out = {}
  for ti, tab in ipairs(tabs or {}) do
    for ai, a in ipairs(tab.actions or {}) do
      if picked[a.id] then
        out[#out+1] = {action = clone_table(a), tab_index = ti, action_index = ai, id = a.id}
      end
    end
  end
  return out
end

local function copy_picked_actions(cut)
  local items = collect_picked_actions()
  if #items == 0 then
    status = "Sélectionne une ou plusieurs cues par leur titre avant Ctrl/Cmd+C ou X."
    return
  end
  cue_clipboard = items
  clipboard_cut = cut and true or false
  if cut then
    local ids = {}
    for _, item in ipairs(items) do ids[item.id] = true end
    for _, tab in ipairs(tabs or {}) do
      local kept = {}
      for _, a in ipairs(tab.actions or {}) do
        if not ids[a.id] then kept[#kept+1] = a end
      end
      tab.actions = kept
    end
    sync_active_tab()
    picked, pick_anchor = {}, nil
    if selected and ids[selected] then selected = nil end
    save()
    status = tostring(#items) .. " cue(s) coupée(s). Colle avec Ctrl/Cmd+V."
  else
    status = tostring(#items) .. " cue(s) copiée(s). Colle avec Ctrl/Cmd+V."
  end
end

local function paste_picked_actions()
  if type(cue_clipboard) ~= "table" or #cue_clipboard == 0 then
    status = "Le presse-papiers des cues est vide."
    return
  end
  local pasted_ids = {}
  for _, item in ipairs(cue_clipboard) do
    local a = clone_table(item.action or item)
    if not clipboard_cut then
      a.id = next_id
      next_id = next_id + 1
    end
    actions[#actions+1] = a
    pasted_ids[a.id] = true
    selected = a.id
  end
  picked = pasted_ids
  pick_anchor = #actions
  if clipboard_cut then
    cue_clipboard, clipboard_cut = nil, false
  end
  save()
  status = tostring((function() local n=0; for _ in pairs(pasted_ids) do n=n+1 end; return n end)()) .. " cue(s) collée(s) dans « " .. tostring(tabs[active_tab].name or "liste active") .. " »."
end

local function move_rows(from, to)
  if not from or not to or not actions[from] then return end
  local ids = {}
  if picked[actions[from].id] then
    for _, a in ipairs(actions) do
      if picked[a.id] then ids[a.id] = true end
    end
  else
    ids[actions[from].id] = true
  end
  local moving, staying = {}, {}
  local orig_first
  for i, a in ipairs(actions) do
    if ids[a.id] then
      moving[#moving+1] = a
      if not orig_first then orig_first = i end
    else
      staying[#staying+1] = a
    end
  end
  if #moving == 0 then return end
  local before = 0
  for i = 1, to-1 do
    if ids[actions[i].id] then before = before + 1 end
  end
  local insert_at = math.max(1, math.min(to - before, #staying + 1))
  if orig_first == insert_at then
    local identical = true
    for i, a in ipairs(moving) do
      if actions[orig_first + i - 1] ~= a then identical = false break end
    end
    if identical then return end
  end
  for i, a in ipairs(moving) do
    table.insert(staying, insert_at + i - 1, a)
  end
  actions = staying
  save()
end

local function go_selected()
  local si
  for i, a in ipairs(actions) do if a.id == selected then si = i end end
  if not si then status = "Aucune action sélectionnée." return end
  fire(actions[si])
  if actions[si+1] then
    pick_only(actions[si+1], si+1)
  end
end

local TYPE_LABEL = {cue="CUE", preset="PRESET", stop="STOP", pause="PAUSE", devamp="DEVAMP", osc="OSC", midi="MIDI"}

local function track_combo(label, guid, allow_none)
  local tr = find_track(guid)
  local preview = tr and track_name(tr) or (allow_none and "(piste d'origine)" or "(choisir)")
  local changed, new = false, guid
  if reaper.ImGui_BeginCombo(ctx, label, preview) then
    if allow_none and reaper.ImGui_Selectable(ctx, "(piste d'origine)##none", guid == nil) then
      new, changed = nil, true
    end
    for i = 0, reaper.CountTracks(PROJ)-1 do
      local t = reaper.GetTrack(PROJ, i)
      local g = reaper.GetTrackGUID(t)
      local folder = reaper.GetMediaTrackInfo_Value(t, "I_FOLDERDEPTH") == 1 and " [dossier]" or ""
      if reaper.ImGui_Selectable(ctx, (i+1)..". "..track_name(t)..folder.."##"..g, g == guid) then
        new, changed = g, true
      end
    end
    reaper.ImGui_EndCombo(ctx)
  end
  return changed, new
end

default_track_guid = function()
  -- Destination par défaut : première piste EXISTANTE du projet.
  -- Ne jamais créer de piste automatiquement lors de l'import ou du lancement.
  local tr = reaper.GetTrack(PROJ, 0)
  if tr then return reaper.GetTrackGUID(tr) end
  return nil
end

local function add_action(t)
  local names = {cue="Cue", preset="Preset", stop="Stop cues", pause="Pause", devamp="Devamp", osc="OSC", midi="MIDI"}
  local a = {id = next_id, type = t, name = names[t].." "..next_id}
  if t == "cue" then a.fadein = 0; a.track = default_track_guid() end
  if t == "stop" then a.dur = 1.0 end
  if t == "pause" then a.dur = 0.5; a.unpause = false end
  if t == "preset" then a.dur = 0.0; a.use = {vol=true, pan=true, fxen=true, fxpar=true} end
  if t == "osc" then a.port_name = ""; a.address = "/"; a.args = {} end
  if t == "midi" then
    a.midi_type = "note"; a.channel = 1
    a.note = 60; a.velocity = 100; a.cc = 1; a.value = 0; a.program = 0
  end
  next_id = next_id + 1
  local pos = #actions + 1
  for i, x in ipairs(actions) do if x.id == selected then pos = i + 1 end end
  table.insert(actions, pos, a)
  pick_only(a, pos)
  save()
end

---------------------------------------------------------------- Snap editor
local function draw_snap_editor(a)
  ensure_snap(a)
  a.use = a.use or {vol=true, pan=true, fxen=true, fxpar=true}
  if reaper.ImGui_Button(ctx, "Capturer les pistes sélectionnées") then
    local n = reaper.CountSelectedTracks(PROJ)
    if n == 0 then
      status = "Sélectionne d'abord une ou plusieurs pistes dans REAPER."
    else
      local snap = {order={}, tracks={}}
      for k = 0, n-1 do snap_add(snap, reaper.GetSelectedTrack(PROJ, k)) end
      a.snap = snap
      save()
      status = n.." piste(s) capturée(s)."
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Capturer toutes les pistes") then
    local snap = {order={}, tracks={}}
    for k = 0, reaper.CountTracks(PROJ)-1 do snap_add(snap, reaper.GetTrack(PROJ, k)) end
    a.snap = snap
    save()
    status = #snap.order.." piste(s) capturée(s)."
  end
  if not a.snap or #a.snap.order == 0 then
    reaper.ImGui_TextDisabled(ctx, "Rien de capturé. Sélectionne des pistes, règle-les, puis clique sur Capturer.")
  else
    reaper.ImGui_Text(ctx, string.format("Capturé : %d piste(s). Décoche celles à ignorer :", #a.snap.order))
    for _, g in ipairs(a.snap.order) do
      local st = a.snap.tracks[g]
      local x
      x, st.include = reaper.ImGui_Checkbox(ctx, (st.name or "?").."##inc"..g, st.include ~= false)
      if x then save() end
    end
    reaper.ImGui_Spacing(ctx)
    reaper.ImGui_Text(ctx, "Ce que le preset rappelle :")
    local u = a.use
    local x
    x, u.vol   = reaper.ImGui_Checkbox(ctx, "Volume", u.vol)   ; if x then save() end
    reaper.ImGui_SameLine(ctx)
    x, u.pan   = reaper.ImGui_Checkbox(ctx, "Pan", u.pan)     ; if x then save() end
    reaper.ImGui_SameLine(ctx)
    x, u.fxen  = reaper.ImGui_Checkbox(ctx, "FX actif/bypass", u.fxen) ; if x then save() end
    reaper.ImGui_SameLine(ctx)
    x, u.fxpar = reaper.ImGui_Checkbox(ctx, "Paramètres FX", u.fxpar) ; if x then save() end
    if reaper.ImGui_TreeNode(ctx, "Détail des effets##fxdetail") then
      for _, g in ipairs(a.snap.order) do
        local st = a.snap.tracks[g]
        if #(st.fx or {}) > 0 then
          reaper.ImGui_Text(ctx, st.name or "?")
          for k, f in ipairs(st.fx) do
            local y
            y, f.use = reaper.ImGui_Checkbox(ctx,
              k..". "..f.name..(f.enabled and " (actif)" or " (bypass)").."##fx"..g..k, f.use)
            if y then save() end
          end
        end
      end
      reaper.ImGui_TreePop(ctx)
    end
  end
end

---------------------------------------------------------------- Forme d'onde
local DB_MIN, DB_MAX = -60, 12
local C_LEFT, C_RIGHT = reaper.ImGui_MouseButton_Left(), reaper.ImGui_MouseButton_Right()

local function get_wave(file)
  local w = wave_cache[file]
  if w then return w end
  w = {}
  wave_cache[file] = w
  local src = reaper.PCM_Source_CreateFromFile(file)
  if not src then w.err = "Fichier illisible." return w end
  local len = reaper.GetMediaSourceLength(src)
  if not len or len <= 0 then
    reaper.PCM_Source_Destroy(src)
    w.err = "Durée inconnue (sous-projet ?) : pas de forme d'onde."
    return w
  end
  w.len = len
  w.nch_full = reaper.GetMediaSourceNumChannels(src)
  local nch = math.max(1, math.min(2, w.nch_full))
  local N = 1200
  local buf = reaper.new_array(N * nch * 2)
  buf.clear()
  local ret = reaper.PCM_Source_GetPeaks(src, N / len, 0, nch, N, 0, buf)
  reaper.PCM_Source_Destroy(src)
  local cnt = math.floor(ret) & 0xFFFFF
  if cnt <= 0 then w.err = "Forme d'onde indisponible." return w end
  w.max, w.min, w.n = {}, {}, cnt
  for sidx = 1, cnt do
    local mx, mn = -1, 1
    for c = 0, nch-1 do
      local vmax = buf[(sidx-1)*nch + c + 1]
      local vmin = buf[N*nch + (sidx-1)*nch + c + 1]
      if vmax > mx then mx = vmax end
      if vmin < mn then mn = vmin end
    end
    w.max[sidx] = math.max(-1, math.min(1, mx))
    w.min[sidx] = math.max(-1, math.min(1, mn))
  end
  return w
end

local function g_to_frac(g)
  local db = (g <= 0.001) and DB_MIN or 20 * math.log(g, 10)
  db = math.max(DB_MIN, math.min(DB_MAX, db))
  return (db - DB_MIN) / (DB_MAX - DB_MIN)
end

local function frac_to_g(f)
  f = math.max(0, math.min(1, f))
  local db = DB_MIN + f * (DB_MAX - DB_MIN)
  if db <= DB_MIN + 0.5 then return 0 end
  if math.abs(db) < 0.7 then return 1 end
  return 10 ^ (db / 20)
end

local function apply_cue_changes(a)
  if a.type == "cue" and runs[a.id] and runs[a.id].loop then
    replan_loop_run(a, runs[a.id])
    return
  end
  if a.type == "cue" and runs[a.id] then
    local r = runs[a.id]
    r.tin = a.inpt
    r.seg = a.outpt - a.inpt
    r.speed = math.max(0.01, math.min(16, tonumber(a.wave_speed) or 1))
    r.proj_seg = r.seg / r.speed
    local it = r.item
    if it and reaper.ValidatePtr2(PROJ, it, "MediaItem*") then
      local tk = reaper.GetActiveTake(it)
      if tk then
        reaper.SetMediaItemInfo_Value(it, "D_LENGTH", r.proj_seg)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_STARTOFFS", r.tin)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_PLAYRATE", r.speed)
        -- Propager les réglages à la lecture active et à tous les items déjà créés
        -- pour cette cue (notamment les répétitions d'une cue en boucle).
        r.env = a.env or r.env or {}
        r.markers = a.markers or r.markers or {}
        if r.loop then r.next = math.max(r.next or 0, r.t0 + r.proj_seg) end
        local pnow = now_pos()
        local elapsed = math.max(0, pnow - (r.t0 or pnow))
        local rel = r.loop and (r.proj_seg > 0 and (elapsed % r.proj_seg) or 0) or math.min(elapsed, r.proj_seg)
        local gain = env_gain(r.env, r.tin + rel * r.speed)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", gain)
        local dest = find_track(r.dest_guid)
        if dest then
          for ii = 0, reaper.CountTrackMediaItems(dest) - 1 do
            local other = reaper.GetTrackMediaItem(dest, ii)
            local _, cid = reaper.GetSetMediaItemInfo_String(other, "P_EXT:cuelist_id", "", false)
            if cid == tostring(a.id) then
              local otk = reaper.GetActiveTake(other)
              if otk then
                local opos = reaper.GetMediaItemInfo_Value(other, "D_POSITION")
                local olen = reaper.GetMediaItemInfo_Value(other, "D_LENGTH")
                reaper.SetMediaItemTakeInfo_Value(otk, "D_STARTOFFS", r.tin)
                reaper.SetMediaItemTakeInfo_Value(otk, "D_PLAYRATE", r.speed)
                if math.abs(olen - r.proj_seg) > 0.001 then reaper.SetMediaItemInfo_Value(other, "D_LENGTH", r.proj_seg) end
                local local_t = r.tin + math.max(0, pnow - opos) * r.speed
                if r.loop and r.seg > 0 then local_t = r.tin + ((local_t - r.tin) % r.seg) end
                reaper.SetMediaItemTakeInfo_Value(otk, "D_VOL", env_gain(r.env, local_t))
                reaper.UpdateItemInProject(other)
              end
            end
          end
        end
        local fo = reaper.GetMediaItemInfo_Value(it, "D_FADEOUTLEN")
        if fo > r.proj_seg then
          reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", r.proj_seg)
        end
        reaper.UpdateItemInProject(it)
      end
    end
  end
end

-- Extensions audio / vidéo acceptées au glisser-déposer (lisibles par REAPER).
X.MEDIA_EXT = {}
for e in ([[wav wave bwf w64 rf64 aif aiff aifc caf au snd flac ogg oga opus mp3 mp2 m4a aac wma wv ape mka
  mp4 m4v mov mkv avi mpg mpeg mpe mxf ts mts m2ts m2v 3gp 3g2 ogv webm wmv flv vob]]):gmatch("%S+") do
  X.MEDIA_EXT[e] = true
end
function X.path_is_media(path)
  local ext = path and path:lower():match("%.([%w]+)$")
  return ext ~= nil and X.MEDIA_EXT[ext] == true
end

local function assign_audio_file(a, f)
  if not f or f == "" then return end
  -- Le nom de la cue reprend le nom du fichier, sans son extension.
  local base = f:gsub("\\", "/"):match("([^/]+)$") or f
  base = base:gsub("%.[^%.]+$", "")
  if base ~= "" then a.name = base end
  a.file, a.inpt, a.outpt, a.env = f, nil, nil, nil
  a.markers, a.marker_name = {}, "Q1"
  a.view_zoom, a.view_offset = 1.0, 0.0
  marker_drag, wf_drag, cv_drag = nil, nil, nil
  wave_cache[f] = nil
  save()
end

-- ReaImGui 0.1.x supports native file-drop payloads. Call this only directly
-- after an ImGui item (for example an InvisibleButton) has been submitted.
local function accept_audio_file_drop(a)
  if not reaper.ImGui_BeginDragDropTarget or not reaper.ImGui_AcceptDragDropPayloadFiles
      or not reaper.ImGui_GetDragDropPayloadFile or not reaper.ImGui_EndDragDropTarget then
    return false
  end
  if not reaper.ImGui_BeginDragDropTarget(ctx) then return false end
  local ok, count = reaper.ImGui_AcceptDragDropPayloadFiles(ctx, nil, (reaper.ImGui_DragDropFlags_None and reaper.ImGui_DragDropFlags_None() or 0))
  if ok and count and count > 0 then
    local chosen, unsupported = nil, nil
    for i = 0, count - 1 do
      local got, path = reaper.ImGui_GetDragDropPayloadFile(ctx, i)
      if got and path and path ~= "" then
        if X.path_is_media(path) then
          chosen = path
          break
        else
          unsupported = path
        end
      end
    end
    if chosen then
      assign_audio_file(a, chosen)
      status = "Fichier audio chargé par glisser-déposer."
    elseif unsupported then
      status = "Format non reconnu : dépose un fichier audio ou vidéo compatible avec REAPER."
    end
  end
  reaper.ImGui_EndDragDropTarget(ctx)
  return ok and count and count > 0 or false
end

-- Dépose d'un fichier sur une ligne de la liste : crée une nouvelle cue Fichier
-- juste après la ligne visée, avec sa propre piste REAPER nommée comme le fichier.
local function accept_audio_file_drop_create(insert_index)
  if not reaper.ImGui_BeginDragDropTarget or not reaper.ImGui_AcceptDragDropPayloadFiles
      or not reaper.ImGui_GetDragDropPayloadFile or not reaper.ImGui_EndDragDropTarget then
    if not file_drop_api_warning_shown then
      status = "Glisser-déposer de fichiers indisponible : mets ReaImGui à jour via ReaPack."
      file_drop_api_warning_shown = true
    end
    return false
  end
  if not reaper.ImGui_BeginDragDropTarget(ctx) then
    -- Diagnostic visible : les fonctions existent, mais cet item n'est pas reconnu
    -- comme cible active par ReaImGui au moment de l'appel.
    if reaper.ImGui_IsItemHovered and reaper.ImGui_IsItemHovered(ctx) then
      status = "Diagnostic dépôt : titre survolé, mais la cible ImGui n'est pas activée."
    end
    return false
  end
  status = "Diagnostic dépôt : cible titre active, attente du fichier…"
  local flags = (reaper.ImGui_DragDropFlags_None and reaper.ImGui_DragDropFlags_None() or 0)
  local ok, count = reaper.ImGui_AcceptDragDropPayloadFiles(ctx, nil, flags)
  if ok then status = "Diagnostic dépôt : payload accepté, nombre de fichiers = " .. tostring(count or 0) end
  local created = false
  if ok and count and count > 0 then
    -- Plusieurs fichiers déposés d'un coup : une cue par fichier compatible,
    -- insérées dans l'ordre juste après la ligne visée.
    local files, rejected = {}, 0
    for fi = 0, count - 1 do
      local got, path = reaper.ImGui_GetDragDropPayloadFile(ctx, fi)
      if got and path and path ~= "" then
        if X.path_is_media(path) then files[#files+1] = path else rejected = rejected + 1 end
      end
    end
    if #files > 0 then
      -- Le fichier est affecté à la première piste existante du projet.
      -- Aucun ajout de piste et aucun renommage de piste lors du dépôt.
      local guid = default_track_guid()
      local pos = math.max(1, math.min(#actions + 1, (insert_index or #actions) + 1))
      local first_pos, new_ids = pos, {}
      for _, chosen in ipairs(files) do
        local base = chosen:gsub("\\", "/"):match("([^/]+)$") or chosen
        base = base:gsub("%.[^%.]+$", "")
        local a = {id=next_id, type="cue", name=base, src="file", file=chosen,
          track=guid, fadein=0, inpt=0, outpt=nil, env=nil, markers={}, marker_name="Q1",
          view_zoom=1.0, view_offset=0.0}
        next_id = next_id + 1
        table.insert(actions, pos, a)
        assign_audio_file(a, chosen)
        new_ids[#new_ids+1] = a.id
        pos = pos + 1
      end
      -- Tout le lot est sélectionné ; la première cue est la cue préparée / éditée.
      picked = {}
      for _, id in ipairs(new_ids) do picked[id] = true end
      pick_anchor = first_pos
      selected = new_ids[1]
      save()
      local extra = rejected > 0 and (" (" .. rejected .. " fichier(s) ignoré(s) : format non reconnu)") or ""
      if #files == 1 then
        status = guid and ("Cue fichier créée : " .. actions[first_pos].name .. " (première piste du projet)." .. extra)
          or ("Cue créée : " .. actions[first_pos].name .. ", mais le projet ne contient aucune piste.")
      else
        status = #files .. " cues créées" .. (guid and " (première piste du projet)" or " (le projet ne contient aucune piste)") .. "." .. extra
      end
      created = true
    else
      status = "Format non reconnu : dépose un fichier audio ou vidéo compatible avec REAPER."
    end
  end
  reaper.ImGui_EndDragDropTarget(ctx)
  return created
end

local function apply_wave_cue_props(a)
  if not a or not a.id then return end
  local gain_db = tonumber(a.wave_gain_db) or 0
  local gain = 10 ^ (gain_db / 20)
  local pan = math.max(-1, math.min(1, tonumber(a.wave_pan) or 0))
  local speed = math.max(0.01, math.min(16, tonumber(a.wave_speed) or 1))
  local pitch = tonumber(a.wave_pitch) or 0
  if a.wave_pitch_link then pitch = 12 * (math.log(speed) / math.log(2)) end
  local src_seg = math.max(0.001, (tonumber(a.outpt) or 0) - (tonumber(a.inpt) or 0))
  local proj_len = src_seg / speed
  local changed = 0
  for ti = 0, reaper.CountTracks(PROJ)-1 do
    local tr = reaper.GetTrack(PROJ, ti)
    for ii = 0, reaper.CountTrackMediaItems(tr)-1 do
      local it = reaper.GetTrackMediaItem(tr, ii)
      local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
      if cid == tostring(a.id) then
        local tk = reaper.GetActiveTake(it)
        if tk then
          local startoffs = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS") or 0
          local env_base = (type(a.env) == "table" and #a.env > 0) and env_gain(a.env, startoffs) or 1
          reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", env_base * gain)
          reaper.SetMediaItemTakeInfo_Value(tk, "D_PAN", pan)
          local old_rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE")
          if not old_rate or old_rate <= 0 then old_rate = 1 end
          local old_len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
          reaper.SetMediaItemTakeInfo_Value(tk, "D_PLAYRATE", speed)
          reaper.SetMediaItemTakeInfo_Value(tk, "D_PITCH", pitch)
          -- Conserver la portion de source de l'item (Li→Lo, Lo→OUT…) :
          -- seule la durée projet change avec la vitesse.
          reaper.SetMediaItemInfo_Value(it, "D_LENGTH", math.max(0.001, old_len * old_rate / speed))
          reaper.UpdateItemInProject(it)
          changed = changed + 1
        end
      end
    end
  end
  if runs[a.id] then
    local r = runs[a.id]
    r.speed = speed
    r.seg = src_seg
    r.proj_seg = proj_len
    if r.loop then replan_loop_run(a, r) end
  end
  if changed > 0 then reaper.UpdateArrange() end
end

-- Réglages de lecture (gain / pan / vitesse / pitch) : section repliable,
-- placée en bas de l'éditeur de forme d'onde.
function X.draw_play_settings(a)
  reaper.ImGui_Separator(ctx)
  if reaper.ImGui_CollapsingHeader(ctx, "Réglages de lecture (gain, pan, vitesse, pitch)##playset", nil,
      reaper.ImGui_TreeNodeFlags_DefaultOpen()) then
    local cg, gain_db = reaper.ImGui_SliderDouble(ctx, "Gain (dB)##wave_gain", a.wave_gain_db, -60, 12, "%.1f dB")
    if cg then a.wave_gain_db = gain_db; apply_wave_cue_props(a); save() end
    local cp, pan = reaper.ImGui_SliderDouble(ctx, "Pan##wave_pan", a.wave_pan, -1, 1, "%.2f")
    if cp then a.wave_pan = pan; apply_wave_cue_props(a); save() end
    reaper.ImGui_SetNextItemWidth(ctx, S(130))
    local cs, speed = reaper.ImGui_InputDouble(ctx, "Vitesse##wave_speed", a.wave_speed, 0.1, 0.5, "%.3f")
    if cs then a.wave_speed = math.max(0.01, math.min(16, speed)); apply_wave_cue_props(a); save() end
    local cl, linked = reaper.ImGui_Checkbox(ctx, "Lier la hauteur à la vitesse##wave_pitch_link", a.wave_pitch_link)
    if cl then a.wave_pitch_link = linked; apply_wave_cue_props(a); save() end
    if not a.wave_pitch_link then
      reaper.ImGui_SetNextItemWidth(ctx, S(130))
      local cpi, pitch = reaper.ImGui_InputDouble(ctx, "Pitch (demi-tons)##wave_pitch", a.wave_pitch, 1, 4, "%.2f")
      if cpi then a.wave_pitch = math.max(-48, math.min(48, pitch)); apply_wave_cue_props(a); save() end
    else
      local linked_pitch = 12 * (math.log(math.max(0.01, a.wave_speed)) / math.log(2))
      reaper.ImGui_TextDisabled(ctx, string.format("Hauteur liée : %+.2f demi-tons", linked_pitch))
    end
    reaper.ImGui_TextDisabled(ctx, "Ces réglages sont propres à cette cue et s'appliquent à ses items REAPER existants et aux prochaines lectures.")
  end
end

local function draw_wave_editor(a)
  if not a.file or a.file == "" then
    reaper.ImGui_TextDisabled(ctx, "Aucun fichier chargé. Glisse un fichier audio ou vidéo dans la zone ci-dessous.")
    if reaper.ImGui_Button(ctx, "Charger un fichier audio...##wave_load_empty") then
      local ok, f = reaper.GetUserFileNameForRead("", "Fichier audio", "")
      if ok and f ~= "" then assign_audio_file(a, f) end
    end
    local drop_w = math.max(S(260), select(1, reaper.ImGui_GetContentRegionAvail(ctx)) - S(8))
    reaper.ImGui_InvisibleButton(ctx, "##wave_drop_empty", drop_w, S(100))
    local dx, dy = reaper.ImGui_GetItemRectMin(ctx)
    local ex, ey = reaper.ImGui_GetItemRectMax(ctx)
    local ddl = reaper.ImGui_GetWindowDrawList(ctx)
    reaper.ImGui_DrawList_AddRect(ddl, dx, dy, ex, ey, 0xFF777777, 0, 0, S(1))
    reaper.ImGui_DrawList_AddText(ddl, dx + S(16), dy + S(38), 0xFFBBBBBB, "Déposer le fichier audio ici")
    accept_audio_file_drop(a)
    return
  end
  reaper.ImGui_Text(ctx, a.file)
  if reaper.ImGui_Button(ctx, "Remplacer le fichier...##wave_replace") then
    local ok, f = reaper.GetUserFileNameForRead(a.file, "Remplacer le fichier audio", "")
    if ok and f ~= "" then assign_audio_file(a, f) end
  end
  a.wave_gain_db = tonumber(a.wave_gain_db) or 0
  a.wave_pan = tonumber(a.wave_pan) or 0
  a.wave_speed = tonumber(a.wave_speed) or 1
  a.wave_pitch = tonumber(a.wave_pitch) or 0
  a.wave_pitch_link = a.wave_pitch_link and true or false
  reaper.ImGui_Separator(ctx)
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Supprimer fichier##wave_clear") then
    a.file, a.inpt, a.outpt, a.env = nil, nil, nil, nil
    a.markers, a.marker_name = {}, "Q1"
    a.view_zoom, a.view_offset = 1.0, 0.0
    marker_drag, wf_drag, cv_drag = nil, nil, nil
    save()
    -- Le fichier vient d'être retiré : ne pas poursuivre le rendu de la waveform
    -- avec a.file == nil, sinon get_wave(nil) provoque « table index is nil ».
    return
  end
  a.markers = type(a.markers) == "table" and a.markers or {}
  a.marker_name = a.marker_name or "Q1"
  local w = get_wave(a.file)
  if w.err then
    reaper.ImGui_Text(ctx, w.err)
    if reaper.ImGui_SmallButton(ctx, "Réessayer##wv") then wave_cache[a.file] = nil end
    return
  end
  local L = w.len
  a.inpt  = math.max(0, math.min(a.inpt or 0, L - 0.05))
  a.outpt = math.max(a.inpt + 0.05, math.min(a.outpt or L, L))
  -- Li / Lo : bornes de boucle, contraintes dans [IN, OUT]
  if a.loop_in == nil then a.loop_in = a.inpt end
  if a.loop_out == nil then a.loop_out = a.outpt end
  a.loop_in  = math.max(a.inpt, math.min(tonumber(a.loop_in) or a.inpt, a.outpt - 0.01))
  a.loop_out = math.max(a.loop_in + 0.01, math.min(tonumber(a.loop_out) or a.outpt, a.outpt))
  a.env   = a.env or {}

  reaper.ImGui_SetNextItemWidth(ctx, S(180))
  local cmn, marker_name = reaper.ImGui_InputText(ctx, "Nom du marqueur##new_take_marker", a.marker_name)
  if cmn then a.marker_name = marker_name; save() end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Ajouter marqueur##new_take_marker") then
    local name = tostring(a.marker_name or ""):gsub("^%s+", ""):gsub("%s+$", "")
    if name == "" then
      status = "Indique un nom de marqueur avant de l'ajouter."
    else
      local lo = math.max(0, math.min(L, a.inpt or 0))
      local hi = math.max(lo, math.min(L, a.outpt or L))
      local best_t, best_gap = (lo + hi) * 0.5, -1
      local span = hi - lo
      if #a.markers > 0 then
        for n = 1, 120 do
          local candidate = lo + span * (n / 121)
          local nearest = math.huge
          for _, existing in ipairs(a.markers) do
            local et = tonumber(existing.t)
            if et then nearest = math.min(nearest, math.abs(candidate - et)) end
          end
          if nearest > best_gap then best_t, best_gap = candidate, nearest end
        end
      end
      a.markers[#a.markers + 1] = {t = best_t, name = name, color = 0}
      table.sort(a.markers, function(p, q) return (tonumber(p.t) or 0) < (tonumber(q.t) or 0) end)
      save()
      status = string.format("Marqueur %s créé à %.3f s.", name, best_t)
    end
  end
  reaper.ImGui_TextDisabled(ctx, "Molette: naviguer | Ctrl+Molette: zoomer | Ctrl+clic marqueur: supprimer")

  reaper.ImGui_SetNextItemWidth(ctx, S(90))
  local c1, v1 = reaper.ImGui_InputDouble(ctx, "Entrée (s)##in", a.inpt, 0, 0, "%.3f")
  if c1 then
    local old = a.inpt
    a.inpt = math.max(0, math.min(v1, a.outpt - 0.05))
    a.loop_in = math.max(a.inpt, math.min((a.loop_in or a.inpt) + (a.inpt - old), (a.loop_out or a.outpt) - 0.01))
    apply_cue_changes(a); save()
  end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_SetNextItemWidth(ctx, S(90))
  local c2, v2 = reaper.ImGui_InputDouble(ctx, "Sortie (s)##out", a.outpt, 0, 0, "%.3f")
  if c2 then
    local old = a.outpt
    a.outpt = math.max(a.inpt + 0.05, math.min(v2, L))
    a.loop_out = math.max((a.loop_in or a.inpt) + 0.01, math.min((a.loop_out or a.outpt) + (a.outpt - old), a.outpt))
    apply_cue_changes(a); save()
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_SmallButton(ctx, "Tout##full") then
    a.inpt, a.outpt, a.loop_in, a.loop_out = 0, L, 0, L
    apply_cue_changes(a); save()
  end

  local c3, lp = reaper.ImGui_Checkbox(ctx, "Boucle##loop", a.loop or false)
  if c3 then a.loop = lp; save() end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_SetNextItemWidth(ctx, S(50))
  local lc_str = a.loop_count and tostring(a.loop_count) or ""
  local clc, lc_val = reaper.ImGui_InputText(ctx, "×##loopcnt", lc_str)
  if clc then
    local n = tonumber(lc_val)
    a.loop_count = (n and n > 0) and math.floor(n) or nil
    save()
  end
  if reaper.ImGui_IsItemHovered(ctx) then
    reaper.ImGui_SetTooltip(ctx, "Nombre de répétitions Li→Lo.\nVide = infini (jusqu'au STOP / Devamp).")
  end
  reaper.ImGui_SameLine(ctx)
  do
    local run = runs[a.id]
    local dev = run and (run.devamp or run.devamp_armed or devamp_flags[a.id])
    -- Clignote tant que la playhead n'a pas franchi Lo (process_runs coupe le flag).
    if run and run.paused then dev = false end
    local blink = dev and (math.floor(reaper.time_precise() * 3) % 2 == 0)
    if blink then
      reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Button(), 0xE74C3CFF)
      reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_ButtonHovered(), 0xC0392BFF)
    end
    if reaper.ImGui_SmallButton(ctx, "Devamp##devamp") then
      if devamp_run(a.id) then
        -- statut posé par devamp_run
      elseif run and (run.devamp or run.devamp_armed) then
        status = "Devamp déjà armé."
      else
        status = "Devamp : lance d'abord la cue en boucle."
      end
    end
    if blink then reaper.ImGui_PopStyleColor(ctx, 2) end
    if reaper.ImGui_IsItemHovered(ctx) then
      reaper.ImGui_SetTooltip(ctx, "Flag : au prochain passage sur Lo, ne reboucle pas, laisse filer jusqu'à OUT.")
    end
  end
  reaper.ImGui_SameLine(ctx)
  do
    local run = runs[a.id]
    local paused = run and run.paused
    local label = paused and "Reprendre##wave_pause" or "Pause##wave_pause"
    if reaper.ImGui_SmallButton(ctx, label) then
      if run and run.alive then
        if not run.paused then pause_run(a.id, 0) else resume_run(a.id, 0) end
      else
        status = "Pause : aucune lecture en cours pour cette cue."
      end
    end
  end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_TextDisabled(ctx, string.format("fichier %.2f s  |  IN→OUT %.2f s  |  Li→Lo %.2f s",
    L, a.outpt - a.inpt, a.loop_out - a.loop_in))

  local avail_w = select(1, reaper.ImGui_GetContentRegionAvail(ctx))
  local cw = math.max(S(240), avail_w - S(8))
  
  local hb, hw = S(28), S(240) -- bande haute : IN/OUT + Li/Lo empilés
  local x0, y0 = reaper.ImGui_GetCursorScreenPos(ctx)
  local yb0 = y0 + hb
  local yb1 = yb0 + hw
  local yend = yb1
  local dl = reaper.ImGui_GetWindowDrawList(ctx)

  wave_rect_x1, wave_rect_y1, wave_rect_x2, wave_rect_y2 = x0, yb0, x0 + cw, yb1

  a.view_zoom = a.view_zoom or 1.0
  a.view_offset = a.view_offset or 0.0
  local view_w = L / a.view_zoom
  local view_x = math.max(0, math.min(L - view_w, a.view_offset))
  local view_end = view_x + view_w

  local function tx(t) return x0 + ((t - view_x) / view_w) * cw end
  local function xt(x) return view_x + ((x - x0) / cw) * view_w end
  local function ycv(g) return yb1 - g_to_frac(g) * hw end
  local xin, xout = tx(a.inpt), tx(a.outpt)
  local xli, xlo = tx(a.loop_in), tx(a.loop_out)

  local play_t
  local run = runs[a.id]
  if run and (is_playing() or run.paused) then
    play_t = run_source_time(run, now_pos())
  end

  reaper.ImGui_DrawList_AddRectFilled(dl, x0, y0, x0+cw, yb0, 0x24382CFF)
  reaper.ImGui_DrawList_AddRectFilled(dl, x0, yb0, x0+cw, yb1, 0x202020FF)

  local idx_start = math.max(1, math.floor((view_x / L) * w.n))
  local idx_end = math.min(w.n, math.floor((view_end / L) * w.n))
  local idx_span = math.max(1, idx_end - idx_start)
  
  local mid = yb0 + hw/2
  for px = 0, math.floor(cw)-1 do
    local idx = idx_start + math.floor((px / cw) * idx_span)
    local mxv, mnv = w.max[idx], w.min[idx]
    if mxv then
      local ya = mid - mxv * hw/2
      local yb = mid - mnv * hw/2
      if yb - ya < 1 then yb = ya + 1 end
      reaper.ImGui_DrawList_AddLine(dl, x0+px, ya, x0+px, yb, 0x4F7FA8FF)
    end
  end

  for _, db in ipairs({-48, -36, -24, -12, 0}) do
    local yy = yb1 - ((db - DB_MIN)/(DB_MAX - DB_MIN)) * hw
    reaper.ImGui_DrawList_AddLine(dl, x0, yy, x0+cw, yy, db == 0 and 0x808040AA or 0x40404088, 1)
    reaper.ImGui_DrawList_AddText(dl, x0+3, yy - S(13), 0x909090FF, db.." dB")
  end

  local env = a.env
  local line_col = 0xF1C40FFF
  if #env == 0 then
    reaper.ImGui_DrawList_AddLine(dl, tx(a.inpt), ycv(1), tx(a.outpt), ycv(1), line_col, 2)
  else
    local px_, py_ = tx(a.inpt), ycv(env[1].g)
    for _, pt in ipairs(env) do
      local nx = tx(math.max(a.inpt, math.min(a.outpt, pt.t)))
      local ny = ycv(pt.g)
      reaper.ImGui_DrawList_AddLine(dl, px_, py_, nx, ny, line_col, 2)
      px_, py_ = nx, ny
    end
    reaper.ImGui_DrawList_AddLine(dl, px_, py_, tx(a.outpt), ycv(env[#env].g), line_col, 2)
    for _, pt in ipairs(env) do
      reaper.ImGui_DrawList_AddCircleFilled(dl, tx(math.max(a.inpt, math.min(a.outpt, pt.t))), ycv(pt.g), S(5), 0xFFFFFFFF)
    end
  end

  reaper.ImGui_DrawList_AddRectFilled(dl, x0, yb0, xin, yb1, 0x000000AA)
  reaper.ImGui_DrawList_AddRectFilled(dl, xout, yb0, x0+cw, yb1, 0x000000AA)

  -- Surbrillance rouge légère UNIQUEMENT si Li/Lo ≠ IN/OUT
  local loop_distinct = (a.loop_in > a.inpt + 1e-4) or (a.loop_out < a.outpt - 1e-4)
  if loop_distinct and a.loop_out > a.loop_in then
    local xl1 = math.max(x0, xli)
    local xl2 = math.min(x0 + cw, xlo)
    if xl2 > xl1 then
      -- RRGGBBAA : rouge discret
      reaper.ImGui_DrawList_AddRectFilled(dl, xl1, yb0, xl2, yb1, 0xE74C3C28)
    end
  end
  
  -- Lignes verticales IN / OUT (pleine hauteur)
  reaper.ImGui_DrawList_AddLine(dl, xin, y0, xin, yb1, 0x2ECC71FF, 2)
  reaper.ImGui_DrawList_AddLine(dl, xout, y0, xout, yb1, 0xE74C3CFF, 2)

  -- Li / Lo TOUJOURS visibles (positions réelles), traits épais + poignées
  local show_loop_handles = (a.loop_out or 0) > (a.loop_in or 0)
  if show_loop_handles then
    -- Même esthétique que IN/OUT : simple trait vertical (les zones de saisie
    -- invisibles près des tags restent inchangées).
    reaper.ImGui_DrawList_AddLine(dl, xli, y0, xli, yb1, 0xF39C12FF, 2)
    reaper.ImGui_DrawList_AddLine(dl, xlo, y0, xlo, yb1, 0xF39C12FF, 2)
  end

  -- Tags IN / OUT en haut de la bande
  local tag_h = S(14)
  reaper.ImGui_DrawList_AddRectFilled(dl, xin, y0, xin + S(28), y0 + tag_h, 0x2ECC71FF)
  reaper.ImGui_DrawList_AddText(dl, xin + S(4), y0 + 1, 0x000000FF, "IN")
  reaper.ImGui_DrawList_AddRectFilled(dl, xout - S(34), y0, xout, y0 + tag_h, 0xE74C3CFF)
  reaper.ImGui_DrawList_AddText(dl, xout - S(30), y0 + 1, 0xFFFFFFFF, "OUT")

  -- Tags Li / Lo à LEUR position (bande haute, sous IN/OUT si coincidents sinon à xli/xlo)
  if show_loop_handles then
    reaper.ImGui_DrawList_AddRectFilled(dl, xli, y0 + tag_h, xli + S(26), y0 + tag_h * 2, 0xF39C12FF)
    reaper.ImGui_DrawList_AddText(dl, xli + S(4), y0 + tag_h + 1, 0x000000FF, "Li")
    reaper.ImGui_DrawList_AddRectFilled(dl, xlo - S(26), y0 + tag_h, xlo, y0 + tag_h * 2, 0xF39C12FF)
    reaper.ImGui_DrawList_AddText(dl, xlo - S(22), y0 + tag_h + 1, 0x000000FF, "Lo")
  end

  yend = yb1
  if play_t then
    reaper.ImGui_DrawList_AddLine(dl, tx(play_t), y0, tx(play_t), yend, 0xFFFFFFFF, 2)
  end

  local marker_boxes, lane_right = {}, {-math.huge, -math.huge, -math.huge}
  for i, marker in ipairs(a.markers) do
    local mt = tonumber(marker.t)
    local mn = tostring(marker.name or "Marker")
    if mt and mt >= 0 and mt <= L and mt >= view_x and mt <= view_end then
      local mxm = tx(mt)
      local is_q = mn:match("^[Qq]%s*[%d%.]+") ~= nil
      local col = is_q and 0x7F1D1DFF or 0x123B52FF
      local edge = is_q and 0xFFE066FF or 0x66E3FFFF
      local label_h = S(24)
      local handle_h = S(10)
      
      reaper.ImGui_DrawList_AddLine(dl, mxm, yb0, mxm, yb1, edge, S(2))
      
      local tag_w = math.max(S(52), math.min(S(190), S(20) + #mn * S(8)))
      local label_x = math.max(x0, math.min(x0 + cw - tag_w, mxm - tag_w * 0.5))
      local lane = nil
      for l = 1, #lane_right do
        if label_x > lane_right[l] + S(3) then lane = l; break end
      end
      if not lane then lane = ((i - 1) % #lane_right) + 1 end
      lane_right[lane] = math.max(lane_right[lane], label_x + tag_w)
      
      local label_y = yb0 + S(1) + (lane - 1) * (label_h + S(2))
      local handle_top = label_y + label_h
      
      reaper.ImGui_DrawList_AddRectFilled(dl, mxm - S(6), handle_top, mxm + S(6), handle_top + handle_h, edge)
      reaper.ImGui_DrawList_AddRect(dl, mxm - S(6), handle_top, mxm + S(6), handle_top + handle_h, 0xFFFFFFFF, 0, 0, S(1))
      reaper.ImGui_DrawList_AddRectFilled(dl, label_x, label_y, label_x + tag_w, label_y + label_h, col)
      reaper.ImGui_DrawList_AddRect(dl, label_x, label_y, label_x + tag_w, label_y + label_h, edge, 0, 0, S(2))
      reaper.ImGui_DrawList_AddText(dl, label_x + S(7), label_y + S(4), 0xFFFFFFFF, mn)
      
      marker_boxes[#marker_boxes + 1] = {
        idx = i, x = mxm, left = label_x, right = label_x + tag_w,
        top = label_y, bottom = label_y + label_h + handle_h, color = col, name = mn
      }
    end
  end

  reaper.ImGui_SetCursorScreenPos(ctx, x0, y0)
  reaper.ImGui_InvisibleButton(ctx, "##inband", cw, hb)
  if reaper.ImGui_IsItemClicked(ctx, C_LEFT) then
    local mxs, mys = reaper.ImGui_GetMousePos(ctx)
    local mid_y = y0 + tag_h
    local d_in  = math.abs(mxs - xin)
    local d_out = math.abs(mxs - xout)
    local d_li  = show_loop_handles and math.abs(mxs - xli) or 1e9
    local d_lo  = show_loop_handles and math.abs(mxs - xlo) or 1e9
    -- Priorité au plus proche ; rangée bas favorise Li/Lo
    if show_loop_handles and mys >= mid_y then
      local best = math.min(d_li, d_lo, d_in, d_out)
      if best == d_lo then wf_drag = "lo"
      elseif best == d_li then wf_drag = "li"
      elseif best == d_out then wf_drag = "out"
      else wf_drag = "in" end
    else
      local best = math.min(d_in, d_out)
      if show_loop_handles then best = math.min(best, d_li, d_lo) end
      if best == d_out then wf_drag = "out"
      elseif best == d_in then wf_drag = "in"
      elseif best == d_lo then wf_drag = "lo"
      else wf_drag = "li" end
    end
  end

  reaper.ImGui_SetCursorScreenPos(ctx, x0, yb0)
  reaper.ImGui_InvisibleButton(ctx, "##wavebody", cw, hw)
  accept_audio_file_drop(a)
  local area_hover = reaper.ImGui_IsItemHovered(ctx)
  local mx, my = reaper.ImGui_GetMousePos(ctx)
  local body_hover = area_hover and my >= yb0 and my <= yb1

  -- Clic près des poignées Li/Lo en haut de la waveform → drag
  if area_hover and reaper.ImGui_IsItemClicked(ctx, C_LEFT) and show_loop_handles then
    local hsz = S(14)
    if my <= yb0 + hsz * 2 then
      local d_li = math.abs(mx - xli)
      local d_lo = math.abs(mx - xlo)
      if d_li <= hsz or d_lo <= hsz then
        wf_drag = (d_lo < d_li) and "lo" or "li"
      end
    end
  end

  if area_hover then
    local wheel = reaper.ImGui_GetMouseWheel(ctx)
    if wheel ~= 0 then
      local is_ctrl = false
      if reaper.ImGui_GetKeyMods and reaper.ImGui_Mod_Ctrl then
        is_ctrl = (reaper.ImGui_GetKeyMods(ctx) & reaper.ImGui_Mod_Ctrl()) ~= 0
      else
        is_ctrl = reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftCtrl()) or reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightCtrl())
      end
      
      local mouse_t = xt(mx)
      if is_ctrl then
        local old_zoom = a.view_zoom
        a.view_zoom = math.max(1.0, math.min(50.0, old_zoom * (1 + wheel * 0.1)))
        local new_view_w = L / a.view_zoom
        local ratio = (mouse_t - view_x) / view_w
        a.view_offset = mouse_t - ratio * new_view_w
      else
        a.view_offset = a.view_offset - wheel * (view_w * 0.05)
      end
      
      a.view_offset = math.max(0, math.min(L - (L / a.view_zoom), a.view_offset))
      view_w = L / a.view_zoom
      view_x = a.view_offset
      view_end = view_x + view_w
    end
  end

  local function hit_point()
    local hit, best_d
    for i, pt in ipairs(env) do
      local dx, dy = math.abs(mx - tx(pt.t)), math.abs(my - ycv(pt.g))
      if dx <= S(8) and dy <= S(8) then
        local d = dx * dx + dy * dy
        if not best_d or d < best_d then hit, best_d = i, d end
      end
    end
    return hit
  end

  local function hit_marker()
    local hit, best_d
    for _, box in ipairs(marker_boxes) do
      local in_label = mx >= box.left - S(3) and mx <= box.right + S(3)
        and my >= box.top - S(3) and my <= box.bottom + S(3)
      if in_label then
        local d = math.abs(mx - box.x)
        if not best_d or d < best_d then hit, best_d = box.idx, d end
      end
    end
    return hit
  end

  local clicked_left = reaper.ImGui_IsItemClicked(ctx, C_LEFT)
  local clicked_right = reaper.ImGui_IsItemClicked(ctx, C_RIGHT)
  if clicked_left or clicked_right then
    local marker_hit = hit_marker()
    local in_wave_body = my >= yb0 and my <= yb1
    local curve_hit = in_wave_body and hit_point() or nil
    local ctrl = false
    local alt = false
    if reaper.ImGui_GetKeyMods then
      local mods = reaper.ImGui_GetKeyMods(ctx)
      if reaper.ImGui_Mod_Alt then alt = (mods & reaper.ImGui_Mod_Alt()) ~= 0 end
    end
    if reaper.ImGui_GetKeyMods and reaper.ImGui_Mod_Ctrl then
      local mods = reaper.ImGui_GetKeyMods(ctx)
      ctrl = (mods & reaper.ImGui_Mod_Ctrl()) ~= 0
    else
      ctrl = reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftCtrl())
        or reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightCtrl())
    end

    if in_wave_body and clicked_left and not alt and not ctrl then
      -- Clic normal = seek source, même si la courbe de volume passe sous le pointeur.
      local source_t = math.max(a.inpt, math.min(a.outpt, xt(mx)))
      local run = runs[a.id]
      if run and is_playing() then
        local speed = math.max(0.01, run.speed or tonumber(a.wave_speed) or 1)
        local project_t = (tonumber(run.t0) or now_pos())
          + (source_t - (tonumber(run.tin) or tonumber(a.inpt) or 0)) / speed
        reaper.SetEditCurPos2(PROJ, project_t, false, true)
        status = string.format("Lecture déplacée à %.3f s.", source_t)
      else
        status = "Clic : la cue doit être en lecture pour déplacer sa tête de lecture."
      end
      cv_drag, marker_drag = nil, nil
    elseif marker_hit then
      if clicked_right or ctrl then
        local removed = table.remove(a.markers, marker_hit)
        marker_drag, cv_drag = nil, nil
        save()
        status = "Marqueur " .. tostring(removed and removed.name or "") .. " supprimé."
      elseif clicked_left then
        marker_drag = {id = a.id, idx = marker_hit, offset = (tonumber(a.markers[marker_hit].t) or xt(mx)) - xt(mx)}
        cv_drag = nil
        status = "Déplacement du marqueur " .. tostring(a.markers[marker_hit].name or "") .. "."
      end
    elseif in_wave_body and (alt or clicked_right or ctrl) then
      if clicked_right then
        if curve_hit then table.remove(env, curve_hit); save() end
      elseif ctrl then
        cv_drag, marker_drag = nil, nil
        if curve_hit then
          table.remove(env, curve_hit)
          save()
          status = "Point de courbe supprimé."
        end
      elseif clicked_left and alt then
        marker_drag = nil
        local hit = curve_hit
        if not hit then
          local t = math.max(a.inpt, math.min(a.outpt, xt(mx)))
          table.insert(env, {t = t, g = frac_to_g(1 - (my - yb0)/hw)})
          table.sort(env, function(p,q) return p.t < q.t end)
          for i, pt in ipairs(env) do if pt.t == t then hit = i end end
        end
        cv_drag = hit and {idx = hit} or nil
      end
    end
  end

  mx, my = reaper.ImGui_GetMousePos(ctx)
  if marker_drag then
    if marker_drag.id ~= a.id then
      marker_drag = nil
    elseif reaper.ImGui_IsMouseDown(ctx, C_LEFT) then
      local marker = a.markers[marker_drag.idx]
      if marker then marker.t = math.max(0, math.min(L, xt(mx) + (marker_drag.offset or 0))) end
    else
      marker_drag = nil
      table.sort(a.markers, function(p, q) return (tonumber(p.t) or 0) < (tonumber(q.t) or 0) end)
      save()
      status = "Position des marqueurs enregistrée."
    end
  end
  if wf_drag then
    if reaper.ImGui_IsMouseDown(ctx, C_LEFT) then
      local t = math.max(0, math.min(L, xt(mx)))
      if wf_drag == "in" then
        local old = a.inpt
        a.inpt = math.min(t, a.outpt - 0.05)
        -- Li suit IN dans les deux sens (delta), restant dans [IN, Lo]
        a.loop_in = math.max(a.inpt, math.min(a.loop_in + (a.inpt - old), a.loop_out - 0.01))
      elseif wf_drag == "out" then
        local old = a.outpt
        a.outpt = math.max(t, a.inpt + 0.05)
        -- Lo suit OUT dans les deux sens
        a.loop_out = math.max(a.loop_in + 0.01, math.min(a.loop_out + (a.outpt - old), a.outpt))
      elseif wf_drag == "li" then
        -- Désolidarisé : ne bouge pas IN
        a.loop_in = math.max(a.inpt, math.min(t, a.loop_out - 0.01))
      elseif wf_drag == "lo" then
        a.loop_out = math.max(a.loop_in + 0.01, math.min(t, a.outpt))
      end
      apply_cue_changes(a)
    else
      wf_drag = nil
      reaper.UpdateArrange()
      save()
    end
  end
  if cv_drag then
    if reaper.ImGui_IsMouseDown(ctx, C_LEFT) then
      local pt = env[cv_drag.idx]
      if pt then
        local lo = env[cv_drag.idx-1] and (env[cv_drag.idx-1].t + 0.001) or a.inpt
        local hi = env[cv_drag.idx+1] and (env[cv_drag.idx+1].t - 0.001) or a.outpt
        pt.t = math.max(lo, math.min(hi, xt(mx)))
        pt.g = frac_to_g(1 - (my - yb0)/hw)
        apply_cue_changes(a)
      end
    else
      cv_drag = nil
      reaper.UpdateArrange()
      save()
    end
  end

  if body_hover then
    local g = frac_to_g(1 - (my - yb0)/hw)
    reaper.ImGui_Text(ctx, string.format("t = %.3f s   gain = %s", xt(mx),
      g <= 0 and "-inf" or string.format("%.1f dB", 20*math.log(g,10))))
  else
    reaper.ImGui_TextDisabled(ctx, "IN/OUT (tags verts/rouges)  |  Li/Lo (tags orange, suivent la sélection)  |  rouge léger = zone de boucle")
  end
  reaper.ImGui_TextDisabled(ctx, "Clic = tête de lecture  |  Alt+clic = courbe  |  Ctrl+clic = supprimer un point")
  if reaper.ImGui_SmallButton(ctx, "Réinitialiser la courbe##envreset") then a.env = {}; save() end

  reaper.ImGui_Separator(ctx)
  reaper.ImGui_Text(ctx, "Marqueurs de la source (temps en secondes)")
  if #a.markers == 0 then
    reaper.ImGui_TextDisabled(ctx, "Aucun marqueur.")
  else
    local remove_marker, markers_changed = nil, false
    for i, marker in ipairs(a.markers) do
      reaper.ImGui_PushID(ctx, 50000 + i)
      reaper.ImGui_SetNextItemWidth(ctx, S(80))
      local ct, mt = reaper.ImGui_InputDouble(ctx, "Temps##marktime", tonumber(marker.t) or 0, 0, 0, "%.3f")
      if ct then marker.t = math.max(0, math.min(L, mt)); markers_changed = true end
      reaper.ImGui_SameLine(ctx)
      reaper.ImGui_SetNextItemWidth(ctx, S(145))
      local cn, mn = reaper.ImGui_InputText(ctx, "Nom##markname", tostring(marker.name or "Marker"))
      if cn then marker.name = mn; markers_changed = true end
      reaper.ImGui_SameLine(ctx)
      if reaper.ImGui_SmallButton(ctx, "Supprimer##markdelete") then remove_marker = i end
      reaper.ImGui_PopID(ctx)
    end
    if remove_marker then
      table.remove(a.markers, remove_marker)
      markers_changed = true
      status = "Marqueur supprimé de la cue."
    end
    if markers_changed then
      table.sort(a.markers, function(p, q) return (tonumber(p.t) or 0) < (tonumber(q.t) or 0) end)
      save()
    end
  end
  reaper.ImGui_TextDisabled(ctx, "Seuls les marqueurs situés entre IN et OUT seront copiés sur l'item.")
  X.draw_play_settings(a)
end

---------------------------------------------------------------- Éditeur d'action
-- Onglet "Preset lié" commun (cue, stop, pause, devamp).
function X.draw_linked_preset_tab(a, time_label)
  local c6, hp = reaper.ImGui_Checkbox(ctx, "Lier un état de pistes à cette action##haspreset", a.has_preset or false)
  if c6 then a.has_preset = hp; save() end
  if a.has_preset then
    draw_snap_editor(a)
    if time_label then
      local c7, lt = reaper.ImGui_Checkbox(ctx, time_label .. "##linktime", a.link_time or false)
      if c7 then a.link_time = lt; save() end
    end
  end
end

-- Sélection des cues ciblées (même mode pour STOP, PAUSE, DEVAMP).
function X.draw_targets_editor(a, kind)
  local verbs = {stop = "arrêter", pause = "mettre en pause / reprendre", devamp = "passer en Devamp"}
  local pre = "##" .. kind .. "_"
  reaper.ImGui_Text(ctx, "IDs des cues à " .. (verbs[kind] or "cibler") .. " (ex. Q1,Q8). Les IDs peuvent appartenir à n'importe quel onglet.")
  local target_text = a.targets_text
  if target_text == nil then
    local parts = {}
    for _, id in ipairs(a.targets or {}) do parts[#parts+1] = "Q" .. tostring(id) end
    target_text = table.concat(parts, ",")
    a.targets_text = target_text
  end
  local ct, new_target_text = reaper.ImGui_InputText(ctx, "IDs ciblés" .. pre .. "targets_text", target_text)
  if ct then
    a.targets_text = new_target_text
    local ids, seen, invalid = {}, {}, false
    for token in (new_target_text .. ","):gmatch("(.-),") do
      local tk = token:match("^%s*(.-)%s*$")
      if tk ~= "" then
        local digits = tk:match("^[Qq]?(%d+)$")
        if digits then
          local id = tonumber(digits)
          if not seen[id] then ids[#ids+1] = id; seen[id] = true end
        else
          invalid = true
        end
      end
    end
    if not invalid then
      a.targets = (#ids > 0) and ids or nil
      a.targets_text_error = nil
      save()
    else
      a.targets_text_error = "Format invalide : utilise Q1,Q8 (IDs numériques séparés par des virgules)."
    end
  end
  if a.targets_text_error then reaper.ImGui_TextColored(ctx, 0xFF4033FF, a.targets_text_error) end

  if reaper.ImGui_Button(ctx, "Capturer les cues sélectionnées (tous onglets)" .. pre .. "capture") then
    local ids = {}
    for _, tab in ipairs(tabs or {}) do
      for _, x in ipairs(tab.actions or {}) do
        if picked[x.id] and x.type == "cue" then ids[#ids+1] = x.id end
      end
    end
    if #ids == 0 then
      status = "Aucune cue sélectionnée dans les onglets."
    else
      a.targets = ids
      local parts = {}; for _, id in ipairs(ids) do parts[#parts+1] = "Q"..tostring(id) end
      a.targets_text = table.concat(parts, ",")
      a.targets_text_error = nil
      save(); status = #ids.." cue(s) ciblée(s)."
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Toutes les cues" .. pre .. "all") then
    a.targets = nil; a.targets_text = ""; a.targets_text_error = nil; save()
  end

  if a.targets and #a.targets > 0 then
    reaper.ImGui_Text(ctx, "Cues ciblées :")
    for _, id in ipairs(a.targets) do
      local nmx, tabname = "(ID introuvable)", "(onglet inconnu)"
      for _, tab in ipairs(tabs or {}) do
        for _, x in ipairs(tab.actions or {}) do
          if tostring(x.id) == tostring(id) then nmx, tabname = (x.name or "Cue"), (tab.name or "Liste"); break end
        end
      end
      reaper.ImGui_BulletText(ctx, string.format("Q%s — %s (%s)", tostring(id), nmx, tabname))
    end
  else
    reaper.ImGui_Text(ctx, "Cible : toutes les cues (aucune liste d'IDs saisie).")
  end
end

local function draw_editor(a, i)
  reaper.ImGui_Separator(ctx)
  local ch, v = reaper.ImGui_InputText(ctx, "Nom", a.name)
  if ch then a.name = v; save() end

  if a.type == "cue" then
    if reaper.ImGui_BeginTabBar(ctx, "cuetabs") then
      if reaper.ImGui_BeginTabItem(ctx, "Source") then
        if reaper.ImGui_RadioButton(ctx, "Région##srcreg", a.src ~= "file") then a.src = "region"; save() end
        reaper.ImGui_SameLine(ctx)
        if reaper.ImGui_RadioButton(ctx, "Fichier##srcfile", a.src == "file") then a.src = "file"; if not find_track(a.track) then a.track = default_track_guid() end; save() end

        if a.src == "file" then
          reaper.ImGui_Text(ctx, (a.file and a.file ~= "") and a.file or "(aucun fichier)")
          if reaper.ImGui_Button(ctx, "Choisir un fichier...") then
            local ok, f = reaper.GetUserFileNameForRead(a.file or "", "Fichier audio", "")
            if ok and f ~= "" then assign_audio_file(a, f) end
          end
          reaper.ImGui_SameLine(ctx)
          if reaper.ImGui_Button(ctx, "Supprimer fichier##source_clear") then
            a.file, a.inpt, a.outpt, a.env = nil, nil, nil, nil
            a.markers, a.marker_name = {}, "Q1"
            a.view_zoom, a.view_offset = 1.0, 0.0
            save()
          end
        else
          local lib = find_project(a.projfn)
          local none = (not a.projfn or a.projfn == "")
          local plabel = none and "(ce projet)" or ((a.projfn:match("([^/\\]+)$") or a.projfn)..(lib and "" or " (non ouvert)"))
          if reaper.ImGui_BeginCombo(ctx, "Projet source##projsrc", plabel) then
            if reaper.ImGui_Selectable(ctx, "(ce projet)##proj0", none) then
              a.projfn, a.region = nil, nil; save()
            end
            for k, o in ipairs(other_projects()) do
              if o.fn ~= "" and reaper.ImGui_Selectable(ctx, o.label.."##proj"..k, a.projfn == o.fn) then
                a.projfn, a.region = o.fn, nil; save()
              end
            end
            reaper.ImGui_EndCombo(ctx)
          end
          local regs = lib and get_regions(lib) or {}
          local preview = "(choisir)"
          for _, r in ipairs(regs) do if r.idx == a.region then preview = r.name end end
          if reaper.ImGui_BeginCombo(ctx, "Région##regcombo", preview) then
            for _, r in ipairs(regs) do
              if reaper.ImGui_Selectable(ctx, r.name.."##r"..r.idx, r.idx == a.region) then
                a.region = r.idx; save()
              end
            end
            reaper.ImGui_EndCombo(ctx)
          end
        end

        local inplace = a.src ~= "file" and a.projfn and a.projfn ~= "" and not a.copy
        if a.src ~= "file" and a.projfn and a.projfn ~= "" then
          local cc, cv = reaper.ImGui_Checkbox(ctx, "Copier les items dans ce projet##copy", a.copy or false)
          if cc then a.copy = cv; save() end
        end

        local c, g = false, a.track
        if inplace then
          reaper.ImGui_TextDisabled(ctx, "La région joue dans son propre onglet (transport + FX du projet source).")
        else
          c, g = track_combo("Piste cible", a.track, a.src ~= "file")
        end
        if c then a.track = g; save() end

        local c4, fi = reaper.ImGui_InputDouble(ctx, "Fade in (s)", a.fadein or 0)
        if c4 then a.fadein = math.max(0, fi); save() end

        reaper.ImGui_Separator(ctx)
        local ca, auto_value = reaper.ImGui_Checkbox(ctx, "AUTO : délai depuis le déclenchement", a.auto == true)
        if ca then a.auto = auto_value; if auto_value then a.follow = false end; save() end
        local cf, follow_value = reaper.ImGui_Checkbox(ctx, "FOLLOW : attendre la fin puis le délai", a.follow == true)
        if cf then a.follow = follow_value; if follow_value then a.auto = false end; save() end
        reaper.ImGui_SetNextItemWidth(ctx, S(110))
        local cd, delay_value = reaper.ImGui_InputDouble(ctx, "DELAY (s)##auto_delay", tonumber(a.delay) or 0, 0, 0, "%.2f")
        if cd then a.delay = math.max(0, delay_value); save() end
        reaper.ImGui_TextDisabled(ctx, "AUTO et FOLLOW sont exclusifs. DELAY s'applique au mode choisi.")

        reaper.ImGui_EndTabItem(ctx)
      end

      -- L'éditeur de waveform ne concerne que les cues utilisant un fichier audio.
      -- En mode région, l'onglet est masqué pour éviter toute confusion.
      if a.src == "file" then
        if reaper.ImGui_BeginTabItem(ctx, "Forme d'onde") then
          draw_wave_editor(a)
          reaper.ImGui_EndTabItem(ctx)
        end
      end

      if reaper.ImGui_BeginTabItem(ctx, "Preset lié") then
        X.draw_linked_preset_tab(a, "Lier le temps du preset au fade in")
        reaper.ImGui_EndTabItem(ctx)
      end
      reaper.ImGui_EndTabBar(ctx)
    end

  elseif a.type == "stop" or a.type == "pause" or a.type == "devamp" then
    if reaper.ImGui_BeginTabBar(ctx, "acttabs_" .. a.type) then
      if reaper.ImGui_BeginTabItem(ctx, "Réglages") then
        if a.type == "stop" then
          local c2, d = reaper.ImGui_InputDouble(ctx, "Durée du fade (s)", a.dur or 1)
          if c2 then a.dur = math.max(0.05, d); save() end
        elseif a.type == "pause" then
          local cu, un = reaper.ImGui_Checkbox(ctx, "Unpause (reprendre les cues en pause)##unpause", a.unpause == true)
          if cu then a.unpause = un; save() end
          if reaper.ImGui_IsItemHovered(ctx) then
            reaper.ImGui_SetTooltip(ctx, "Décochée : met en pause les cues en lecture.\nCochée : reprend les cues en pause.\nAucune action si la cue est déjà dans l'état demandé.")
          end
          local lbl = a.unpause == true and "Fade in après unpause (s)" or "Fade out avant pause (s)"
          local c2, d = reaper.ImGui_InputDouble(ctx, lbl .. "##pausedur", a.dur or 0)
          if c2 then a.dur = math.max(0, d); save() end
          if a.unpause ~= true and (a.dur or 0) > PAUSE_FADE_MAX then
            reaper.ImGui_TextColored(ctx, 0xF39C12FF, string.format("Fade out limité à %.0f s (planification à l'avance).", PAUSE_FADE_MAX))
          end
        else
          reaper.ImGui_TextDisabled(ctx, "Arme le Devamp sur les cues ciblées : elles finissent leur passage jusqu'à Lo puis filent vers OUT.")
        end
        X.draw_targets_editor(a, a.type)
        reaper.ImGui_EndTabItem(ctx)
      end
      if reaper.ImGui_BeginTabItem(ctx, "Preset lié") then
        X.draw_linked_preset_tab(a, a.type == "stop" and "Lier le temps du preset à la durée du fade"
          or (a.type == "pause" and "Lier le temps du preset au fade" or nil))
        reaper.ImGui_EndTabItem(ctx)
      end
      reaper.ImGui_EndTabBar(ctx)
    end

  elseif a.type == "osc" then
    local preview = (a.port_name and a.port_name ~= "") and a.port_name or "(choisir un port)"
    if reaper.ImGui_BeginCombo(ctx, "Port OSC##oscport", preview) then
      for _, p in ipairs(prefs.ports or {}) do
        if reaper.ImGui_Selectable(ctx, p.name.."##p"..p.name, a.port_name == p.name) then
          a.port_name = p.name; save()
        end
      end
      reaper.ImGui_EndCombo(ctx)
    end
    local c, addr = reaper.ImGui_InputText(ctx, "Adresse##oscaddr", a.address or "/")
    if c then a.address = addr; save() end
    reaper.ImGui_TextDisabled(ctx, "Arguments (séparés par des espaces) :")
    local argstr = table.concat(a.args or {}, " ")
    local c2, newargs = reaper.ImGui_InputText(ctx, "##oscargs", argstr)
    if c2 then
      a.args = {}
      for token in newargs:gmatch("%S+") do
        local n = tonumber(token)
        a.args[#a.args+1] = n or token
      end
      save()
    end
    if not has_socket then
      reaper.ImGui_TextColored(ctx, 0xF39C12FF, "LuaSocket manquant → l'envoi OSC est désactivé.")
    end

  elseif a.type == "midi" then
    local c, g = track_combo("Piste cible##miditr", a.track, false)
    if c then a.track = g; save() end
    local types = {"note", "cc", "pc"}
    local labels = {note="Note", cc="Control Change", pc="Program Change"}
    if reaper.ImGui_BeginCombo(ctx, "Type##miditype", labels[a.midi_type or "note"]) then
      for _, t in ipairs(types) do
        if reaper.ImGui_Selectable(ctx, labels[t].."##mt"..t, a.midi_type == t) then
          a.midi_type = t; save()
        end
      end
      reaper.ImGui_EndCombo(ctx)
    end
    local cch, chv = reaper.ImGui_InputInt(ctx, "Canal (1-16)##midich", a.channel or 1)
    if cch then a.channel = math.max(1, math.min(16, chv)); save() end
    if a.midi_type == "note" then
      local cn, nv = reaper.ImGui_InputInt(ctx, "Note (0-127)##midinote", a.note or 60)
      if cn then a.note = math.max(0, math.min(127, nv)); save() end
      local cv, vv = reaper.ImGui_InputInt(ctx, "Velocity##midivel", a.velocity or 100)
      if cv then a.velocity = math.max(0, math.min(127, vv)); save() end
    elseif a.midi_type == "cc" then
      local cc, cv = reaper.ImGui_InputInt(ctx, "CC (0-127)##midicc", a.cc or 1)
      if cc then a.cc = math.max(0, math.min(127, cv)); save() end
      local cv2, vv = reaper.ImGui_InputInt(ctx, "Valeur##midival", a.value or 0)
      if cv2 then a.value = math.max(0, math.min(127, vv)); save() end
    else
      local cp, pv = reaper.ImGui_InputInt(ctx, "Program (0-127)##midiprog", a.program or 0)
      if cp then a.program = math.max(0, math.min(127, pv)); save() end
    end

  else -- preset
    local c2, d = reaper.ImGui_InputDouble(ctx, "Transition (s)", a.dur or 0)
    if c2 then a.dur = math.max(0, d); save() end
    draw_snap_editor(a)
  end

  reaper.ImGui_Spacing(ctx)
  reaper.ImGui_TextDisabled(ctx, "Supprimer : Ctrl/Cmd + clic sur le N° de la ligne.")
end

---------------------------------------------------------------- Préférences
local function draw_prefs()
  if reaper.ImGui_CollapsingHeader(ctx, "Préférences générales") then
    local c1, v1 = reaper.ImGui_Checkbox(ctx, "Arrêter la lecture quand plus aucun média n'est joué", prefs.auto_stop)
    if c1 then prefs.auto_stop = v1; cue_session, idle_since = false, nil; save() end
    local c2, v2 = reaper.ImGui_Checkbox(ctx, "Delete on stop", prefs.delete_on_stop == true)
    if c2 then
      prefs.delete_on_stop = v2 and true or false
      if not prefs.delete_on_stop then
        -- Annuler les suppressions différées en attente.
        del_jobs = {}
      end
      save()
    end
    if reaper.ImGui_IsItemHovered(ctx) then
      reaper.ImGui_SetTooltip(ctx,
        "Coché : les items ActionList sont supprimés après STOP / fin de lecture.\n"
        .. "Décoché : les items restent sur la timeline.\n"
        .. "(L'arrêt de la lecture REAPER dépend de l'option « Arrêter la lecture… ».)")
    end
    local c8, v8 = reaper.ImGui_Checkbox(ctx, "Une nouvelle cue remplace celle qui joue déjà sur la même piste", prefs.exclusive_track ~= false)
    if c8 then prefs.exclusive_track = v8; save() end

    reaper.ImGui_SetNextItemWidth(ctx, S(110))
    local ch, v = reaper.ImGui_InputInt(ctx, "Marge (ms)", margin)
    if ch then
      margin = math.max(0, math.min(2000, v))
      reaper.SetExtState(EXT, "margin", tostring(margin), true)
    end

    reaper.ImGui_Separator(ctx)
    reaper.ImGui_Text(ctx, "Ports OSC (illimités)")
    reaper.ImGui_Spacing(ctx)
    prefs.ports = prefs.ports or {}
    local to_remove = nil
    for i, p in ipairs(prefs.ports) do
      reaper.ImGui_PushID(ctx, "port"..i)
      reaper.ImGui_Text(ctx, "Nom")
      reaper.ImGui_SameLine(ctx, S(80))
      reaper.ImGui_SetNextItemWidth(ctx, S(180))
      local cn, nn = reaper.ImGui_InputText(ctx, "##name", p.name or "")
      if cn then p.name = nn; save() end
      reaper.ImGui_Text(ctx, "IP")
      reaper.ImGui_SameLine(ctx, S(80))
      reaper.ImGui_SetNextItemWidth(ctx, S(180))
      local ci, ni = reaper.ImGui_InputText(ctx, "##ip", p.ip or "127.0.0.1")
      if ci then p.ip = ni; save() end
      reaper.ImGui_Text(ctx, "Port")
      reaper.ImGui_SameLine(ctx, S(80))
      reaper.ImGui_SetNextItemWidth(ctx, S(100))
      local cp, np = reaper.ImGui_InputInt(ctx, "##port", p.port or 8000, 0, 0)
      if cp then p.port = math.max(1, math.min(65535, np)); save() end
      reaper.ImGui_SameLine(ctx)
      if reaper.ImGui_Button(ctx, "Supprimer") then
        to_remove = i
      end
      reaper.ImGui_Spacing(ctx)
      reaper.ImGui_Separator(ctx)
      reaper.ImGui_PopID(ctx)
    end
    if to_remove then
      table.remove(prefs.ports, to_remove)
      save()
    end
    if reaper.ImGui_Button(ctx, "+ Ajouter un port OSC") then
      prefs.ports[#prefs.ports+1] = {
        name = "Port " .. (#prefs.ports + 1),
        ip = "127.0.0.1",
        port = 8000
      }
      save()
    end
    if not has_socket then
      reaper.ImGui_TextColored(ctx, 0xF39C12FF, "Mavriq Lua Sockets 1.2 non détecté → l'envoi OSC est désactivé.")
      reaper.ImGui_TextDisabled(ctx, "Vérifie dans ReaPack que Mavriq Lua Sockets est installé en version 1.2.")
    end
    reaper.ImGui_Separator(ctx)
    reaper.ImGui_SetNextItemWidth(ctx, S(200))
    local cz, zv = reaper.ImGui_SliderDouble(ctx, "Zoom interface##zoom", ui_scale, 0.6, 2.5, "%.2f")
    if cz then set_zoom(zv) end
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_SmallButton(ctx, "100%##zoomreset") then set_zoom(1.0) end
  end
end

---------------------------------------------------------------- Draw principal
local function draw()
  -- Raccourcis clavier traités au début de la frame, avant que les widgets
  -- (boutons, champs de saisie, etc.) ne consomment les événements clavier.
  local focused = false
  if reaper.ImGui_FocusedFlags_RootAndChildWindows then
    focused = reaper.ImGui_IsWindowFocused(ctx, reaper.ImGui_FocusedFlags_RootAndChildWindows())
  else
    focused = reaper.ImGui_IsWindowFocused(ctx)
  end
  local item_active = reaper.ImGui_IsAnyItemActive and reaper.ImGui_IsAnyItemActive(ctx) or false
  if focused and not item_active then
    local shortcut_down = false
    if reaper.ImGui_GetKeyMods and reaper.ImGui_Mod_Shortcut then
      shortcut_down = (reaper.ImGui_GetKeyMods(ctx) & reaper.ImGui_Mod_Shortcut()) ~= 0
    else
      shortcut_down = reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftCtrl())
        or reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightCtrl())
        or (reaper.ImGui_Key_LeftSuper and reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftSuper()))
        or (reaper.ImGui_Key_RightSuper and reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightSuper()))
    end
    if shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_C(), false) then
      copy_picked_actions(false)
    elseif shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_X(), false) then
      copy_picked_actions(true)
    elseif shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_V(), false) then
      paste_picked_actions()
    elseif shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Z(), false) then
      undo_change()
    elseif shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Y(), false) then
      redo_change()
    elseif reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Escape(), false) then
      auto_chain = nil
      fire_stop({dur = stop_fade})
    elseif selected and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Space(), false) then
      go_selected()
    end
  end

  local mx, my = reaper.ImGui_GetMousePos(ctx)
  local over_wave = false
  if wave_rect_x1 then
    if mx >= wave_rect_x1 and mx <= wave_rect_x2 and my >= wave_rect_y1 and my <= wave_rect_y2 then
      over_wave = true
    end
  end

  local _, ctrl = mods_shift_multi()
  if ctrl and not over_wave and reaper.ImGui_IsWindowHovered(ctx, reaper.ImGui_HoveredFlags_ChildWindows()) then
    local wheel = reaper.ImGui_GetMouseWheel(ctx)
    if wheel ~= 0 then set_zoom(ui_scale * (1 + 0.1 * wheel)) end
  end

  -- Barre d'onglets : les carrés sont réordonnables par glisser-déposer.
  for i, tab in ipairs(tabs) do
    if i > 1 then reaper.ImGui_SameLine(ctx) end
    local label = (i == active_tab and "[ " or "") .. (tab.name or ("Liste "..i)) .. (i == active_tab and " ]" or "") .. "##cue_list_tab_"..i
    if reaper.ImGui_Button(ctx, label) and i ~= active_tab then
      active_tab = i; sync_active_tab()
      pick_anchor = nil
      status = "Liste active : " .. (tabs[i].name or ("Liste "..i))
    end
    -- Source : envoyer l'index de l'onglet déplacé.
    if reaper.ImGui_BeginDragDropSource and reaper.ImGui_SetDragDropPayload and reaper.ImGui_EndDragDropSource and reaper.ImGui_BeginDragDropSource(ctx) then
      reaper.ImGui_SetDragDropPayload(ctx, "CUE_LIST_TAB", tostring(i))
      reaper.ImGui_Text(ctx, tab.name or ("Liste "..i))
      reaper.ImGui_EndDragDropSource(ctx)
    end
    -- Cible : déplacer l'onglet lâché à cette position.
    if reaper.ImGui_BeginDragDropTarget and reaper.ImGui_AcceptDragDropPayload and reaper.ImGui_EndDragDropTarget and reaper.ImGui_BeginDragDropTarget(ctx) then
      local accepted, payload = reaper.ImGui_AcceptDragDropPayload(ctx, "CUE_LIST_TAB")
      if accepted and payload then
        local from = tonumber(payload)
        if from and from >= 1 and from <= #tabs and from ~= i then
          local moved = table.remove(tabs, from)
          local dest = i
          if from < i then dest = i - 1 end
          table.insert(tabs, dest, moved)
          if active_tab == from then active_tab = dest
          elseif from < active_tab and dest >= active_tab then active_tab = active_tab - 1
          elseif from > active_tab and dest <= active_tab then active_tab = active_tab + 1 end
          sync_active_tab(); save(); status = "Onglets réorganisés."
        end
      end
      reaper.ImGui_EndDragDropTarget(ctx)
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+##new_cue_list_tab") then
    tabs[#tabs+1] = {name = new_tab_name(), actions = {}}
    active_tab = #tabs; sync_active_tab()
    pick_anchor = nil
    save(); status = "Nouvel onglet créé."
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "-##delete_cue_list_tab") then
    if #tabs <= 1 then status = "Il faut conserver au moins un onglet."
    else pending_delete_tab = active_tab end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Renommer##cue_list_tab") then
    tab_name_edit = active_tab; tab_name_buffer = tabs[active_tab].name or ("Liste "..active_tab)
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Vider liste##clear_active_list") then
    if reaper.MB("Vider uniquement la liste active « " .. tostring(tabs[active_tab].name or "Liste") .. " » ?", "ActionList — Vider liste", 4) == 6 then
      tabs[active_tab].actions = {}
      sync_active_tab()
      picked, pick_anchor, marked, selected = {}, nil, {}, nil
      editor_selected = nil
      save()
      status = "Liste active vidée. Les autres onglets sont conservés."
    end
  end
  if tab_name_edit then
    reaper.ImGui_SameLine(ctx)
    reaper.ImGui_SetNextItemWidth(ctx, S(130))
    local changed, value = reaper.ImGui_InputText(ctx, "Nom##cue_list_tab_name", tab_name_buffer)
    if changed then tab_name_buffer = value end
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_Button(ctx, "OK##cue_list_tab_name") then
      local name = (tab_name_buffer or ""):match("^%s*(.-)%s*$")
      if name ~= "" then tabs[tab_name_edit].name = name; save(); status = "Onglet renommé." end
      tab_name_edit = nil
    end
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_Button(ctx, "Annuler##cue_list_tab_name") then tab_name_edit = nil end
  end
  if pending_delete_tab then
    reaper.ImGui_SameLine(ctx)
    reaper.ImGui_Text(ctx, "Confirmer suppression de « "..(tabs[pending_delete_tab].name or "Liste").." » ?")
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_Button(ctx, "Oui##confirm_delete_tab") then
      table.remove(tabs, pending_delete_tab)
      active_tab = math.min(pending_delete_tab, #tabs); pending_delete_tab = nil
      sync_active_tab(); picked, pick_anchor, marked, selected = {}, nil, {}, nil
      editor_selected = nil
      save(); status = "Onglet supprimé."
    end
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_Button(ctx, "Non##cancel_delete_tab") then pending_delete_tab = nil end
  end
  reaper.ImGui_Separator(ctx)

  local sel_name = "-"
  for _, a in ipairs(actions) do if a.id == selected then sel_name = a.name end end

  local GREEN_GO = 0x2E8B57FF
  local WHITE_GO = 0xFFFFFFFF
  reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Button(), GREEN_GO)
  if reaper.ImGui_Col_ButtonHovered then reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_ButtonHovered(), GREEN_GO) end
  if reaper.ImGui_Col_ButtonActive then reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_ButtonActive(), GREEN_GO) end

  local go_pressed = false
  local go_w, go_h = S(100), S(80)
  local can_draw = reaper.ImGui_GetWindowDrawList
    and reaper.ImGui_GetItemRectMin and reaper.ImGui_GetItemRectMax
  local can_draw_text = can_draw and reaper.ImGui_DrawList_AddTextEx
    and reaper.ImGui_CalcTextSize and reaper.ImGui_GetFontSize
  local can_draw_shapes = can_draw and reaper.ImGui_DrawList_AddCircle
    and reaper.ImGui_DrawList_AddLine and reaper.ImGui_DrawList_AddRectFilled

  if can_draw_text or can_draw_shapes then
    go_pressed = reaper.ImGui_Button(ctx, "##main", go_w, go_h)
    local x1, y1 = reaper.ImGui_GetItemRectMin(ctx)
    local x2, y2 = reaper.ImGui_GetItemRectMax(ctx)
    local dl = reaper.ImGui_GetWindowDrawList(ctx)
    local bw, bh = x2 - x1, y2 - y1
    if can_draw_text then
      local base_size = reaper.ImGui_GetFontSize(ctx)
      local go_font_size = math.max(S(54), 60 * ui_scale)
      local text_w, text_h = reaper.ImGui_CalcTextSize(ctx, "GO")
      local ratio = base_size > 0 and (go_font_size / base_size) or 4.0
      local tw, th = text_w * ratio, text_h * ratio
      local tx = x1 + (bw - tw) * 0.5
      local ty = y1 + (bh - th) * 0.5
      reaper.ImGui_DrawList_AddTextEx(dl, nil, go_font_size, tx, ty, WHITE_GO, "GO")
    else
      local cy = y1 + bh * 0.5
      local r = math.min(bw * 0.235, bh * 0.39)
      local gx, ox = x1 + bw * 0.26, x1 + bw * 0.74
      local thick = math.max(4, S(5))
      reaper.ImGui_DrawList_AddCircle(dl, gx, cy, r, WHITE_GO, 0, thick)
      reaper.ImGui_DrawList_AddRectFilled(dl, gx + 3, cy - thick * 1.1,
        gx + r + thick + 2, cy + thick * 2.4, GREEN_GO)
      reaper.ImGui_DrawList_AddLine(dl, gx + 1, cy + thick * 1.5,
        gx + r, cy + thick * 1.5, WHITE_GO, thick)
      reaper.ImGui_DrawList_AddLine(dl, gx + r - thick * 0.5, cy + thick * 1.5,
        gx + r - thick * 0.5, cy + r * 0.58, WHITE_GO, thick)
      reaper.ImGui_DrawList_AddCircle(dl, ox, cy, r, WHITE_GO, 0, thick)
    end
  else
    local go_font_pushed = false
    if reaper.ImGui_PushFont and reaper.ImGui_PopFont then
      local base_size = reaper.ImGui_GetFontSize and reaper.ImGui_GetFontSize(ctx) or S(13)
      local ok = pcall(reaper.ImGui_PushFont, ctx, nil, math.max(S(54), 60 * ui_scale))
      if ok then
        local actual = reaper.ImGui_GetFontSize and reaper.ImGui_GetFontSize(ctx) or nil
        if actual and actual >= base_size * 1.7 then
          go_font_pushed = true
        else
          pcall(reaper.ImGui_PopFont, ctx)
        end
      end
    end
    if not go_font_pushed and reaper.ImGui_SetWindowFontScale then
      reaper.ImGui_SetWindowFontScale(ctx, math.max(4.0, ui_scale * 4.0))
    end
    go_pressed = reaper.ImGui_Button(ctx, "GO##main", go_w, go_h)
    if go_font_pushed then reaper.ImGui_PopFont(ctx)
    elseif reaper.ImGui_SetWindowFontScale then reaper.ImGui_SetWindowFontScale(ctx, ui_scale) end
  end

  local go_pop_count = 1
  if reaper.ImGui_Col_ButtonHovered then go_pop_count = go_pop_count + 1 end
  if reaper.ImGui_Col_ButtonActive then go_pop_count = go_pop_count + 1 end
  reaper.ImGui_PopStyleColor(ctx, go_pop_count)
  if go_pressed then go_selected() end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_Text(ctx, "Prochaine : "..sel_name)

  if reaper.ImGui_Button(ctx, "+ Cue") then add_action("cue") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Preset") then add_action("preset") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Stop") then add_action("stop") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Pause") then add_action("pause") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Devamp") then add_action("devamp") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ OSC") then add_action("osc") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ MIDI") then add_action("midi") end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_TextDisabled(ctx, "Ctrl/Cmd+C couper/copier · Ctrl/Cmd+V coller")
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Button(), 0xB22222FF)
  if reaper.ImGui_Button(ctx, "STOP (Échap)") then auto_chain = nil; fire_stop({dur = stop_fade}) end
  reaper.ImGui_PopStyleColor(ctx)
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_SetNextItemWidth(ctx, S(80))
  local cf, sf = reaper.ImGui_InputDouble(ctx, "Fade stop (s)", stop_fade)
  if cf then
    stop_fade = math.max(0.05, sf)
    reaper.SetExtState(EXT, "stopfade", tostring(stop_fade), true)
  end

  if reaper.ImGui_Button(ctx, "New") then
    if reaper.MB("Créer une nouvelle session ?\nToutes les listes et tous leurs onglets seront vidés.", "ActionList — Nouvelle session", 4) == 6 then
      for _, tab in ipairs(tabs) do tab.actions = {} end
      sync_active_tab()
      picked, pick_anchor, marked, selected = {}, nil, {}, nil
      editor_selected = nil
      cue_clipboard, clipboard_cut = nil, false
      save()
      status = "Toutes les listes ont été vidées."
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Open") then
    local ok, f = reaper.GetUserFileNameForRead("", "Ouvrir une ActionList", "*.lua;*.txt")
    if ok and f ~= "" then
      local file = io.open(f, "r")
      if file then
        local content = file:read("*a")
        file:close()
        local loader = load("return "..content, "actionlist", "t", {})
        if loader then
          local ok2, d = pcall(loader)
          if ok2 and type(d) == "table" and (type(d.actions) == "table" or type(d.tabs) == "table") then
            next_id  = d.next_id or 1
            if type(d.tabs) == "table" and #d.tabs > 0 then
              tabs = d.tabs
              for _, tab in ipairs(tabs) do tab.name = tab.name or "Liste"; tab.actions = tab.actions or {} end
              active_tab = d.active_tab or 1; sync_active_tab()
            else
              actions = d.actions or {}; tabs = {{name = "Liste 1", actions = actions}}; active_tab = 1; sync_active_tab()
            end
            if type(d.prefs) == "table" then
              for k, pv in pairs(d.prefs) do prefs[k] = pv end
            end
            if not prefs.ports then prefs.ports = {} end
            picked, pick_anchor, marked, selected = {}, nil, {}, nil
      editor_selected = nil
            save()
            status = "ActionList chargée : "..f
          else
            status = "Fichier invalide : "..f
          end
        else
          status = "Impossible d'analyser : "..f
        end
      else
        status = "Impossible d'ouvrir : "..f
      end
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Save") then
    local f = nil
    if reaper.JS_Dialog_BrowseForSaveFile then
      local ok, filename = reaper.JS_Dialog_BrowseForSaveFile("Enregistrer l'ActionList", "", "ActionList.lua", "*.lua;*.txt")
      if ok and filename ~= "" then f = filename end
    else
      local ok, filename = reaper.GetUserFileNameForRead("", "Enregistrer l'ActionList (Taper le nom et valider)", "*.lua;*.txt")
      if ok and filename ~= "" then f = filename end
    end

    if f then
      local file = io.open(f, "w")
      if file then
        file:write(ser({actions = actions, tabs = tabs, active_tab = active_tab, next_id = next_id, prefs = prefs}))
        file:close()
        status = "ActionList enregistrée : "..f
      else
        status = "Impossible d'écrire : "..f
      end
    end
  end
  reaper.ImGui_SameLine(ctx)
  local icon_size = S(28)
  if reaper.ImGui_Button(ctx, "↶##undo", icon_size, icon_size) then undo_change() end
  if reaper.ImGui_IsItemHovered(ctx) then reaper.ImGui_SetTooltip(ctx, "Annuler") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "↷##redo", icon_size, icon_size) then redo_change() end
  if reaper.ImGui_IsItemHovered(ctx) then reaper.ImGui_SetTooltip(ctx, "Rétablir") end

  reaper.ImGui_Separator(ctx)
  draw_prefs()

  -- Aucune cue n'est sélectionnée automatiquement au démarrage ou lorsque
  -- la sélection courante n'existe plus dans la liste. La liste peut rester vide.
  -- Les paramètres affichés sont TOUJOURS ceux de l'action dont le N° est
  -- sélectionné (`selected`). Le clic sur un titre ne fait que remplir la
  -- sélection multiple (`picked`) : on peut ainsi sélectionner des cues par leur
  -- titre puis les capturer dans les paramètres d'un Stop / Pause / Devamp.
  local sel_i
  for i, a in ipairs(actions) do if a.id == selected then sel_i = i; break end end

  if focused then
    local ctrl_down = false
    if reaper.ImGui_GetKeyMods and reaper.ImGui_Mod_Ctrl then
      ctrl_down = (reaper.ImGui_GetKeyMods(ctx) & reaper.ImGui_Mod_Ctrl()) ~= 0
    else
      ctrl_down = reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftCtrl()) or reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightCtrl())
    end
    if sel_i and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_DownArrow()) and actions[sel_i+1] then
      local shift = select(1, mods_shift_multi())
      if shift then
        pick_anchor = pick_anchor or sel_i
        selected = actions[sel_i+1].id
        pick_range(pick_anchor, sel_i+1)
      else
        pick_only(actions[sel_i+1], sel_i+1)
      end
    elseif sel_i and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_UpArrow()) and actions[sel_i-1] then
      local shift = select(1, mods_shift_multi())
      if shift then
        pick_anchor = pick_anchor or sel_i
        selected = actions[sel_i-1].id
        pick_range(pick_anchor, sel_i-1)
      else
        pick_only(actions[sel_i-1], sel_i-1)
      end
    end
  end

  reaper.ImGui_Separator(ctx)
  
  local _, avail_h = reaper.ImGui_GetContentRegionAvail(ctx)
  local list_h = math.max(S(120), avail_h - (lower_h_override or lower_h) - S(8))

  local table_flags = reaper.ImGui_TableFlags_RowBg() |
                      reaper.ImGui_TableFlags_BordersInnerV() |
                      reaper.ImGui_TableFlags_Resizable() |
                      reaper.ImGui_TableFlags_Reorderable() |
                      reaper.ImGui_TableFlags_ScrollY()

  if reaper.ImGui_BeginTable(ctx, "actions_table", 9, table_flags, 0, list_h) then
    reaper.ImGui_TableSetupScrollFreeze(ctx, 0, 1)

    reaper.ImGui_TableSetupColumn(ctx, "N°", reaper.ImGui_TableColumnFlags_WidthFixed(), S(34))
    reaper.ImGui_TableSetupColumn(ctx, "Titre", reaper.ImGui_TableColumnFlags_WidthStretch())
    reaper.ImGui_TableSetupColumn(ctx, "Type", reaper.ImGui_TableColumnFlags_WidthFixed(), S(68))
    reaper.ImGui_TableSetupColumn(ctx, "Statut", reaper.ImGui_TableColumnFlags_WidthFixed(), S(104))
    reaper.ImGui_TableSetupColumn(ctx, "AUTO", reaper.ImGui_TableColumnFlags_WidthFixed(), S(48))
    reaper.ImGui_TableSetupColumn(ctx, "FOLLOW", reaper.ImGui_TableColumnFlags_WidthFixed(), S(58))
    reaper.ImGui_TableSetupColumn(ctx, "DELAY (s)", reaper.ImGui_TableColumnFlags_WidthFixed(), S(86))
    reaper.ImGui_TableSetupColumn(ctx, "Output", reaper.ImGui_TableColumnFlags_WidthFixed(), S(130))
    reaper.ImGui_TableSetupColumn(ctx, "ID", reaper.ImGui_TableColumnFlags_WidthFixed(), S(54))

    reaper.ImGui_TableNextRow(ctx, reaper.ImGui_TableRowFlags_Headers())
    for col, label in ipairs({"N°", "Titre", "Type", "Statut", "AUTO", "FOLLOW", "DELAY (s)", "Output", "ID"}) do
      reaper.ImGui_TableSetColumnIndex(ctx, col - 1)
      reaper.ImGui_TableSetBgColor(ctx, reaper.ImGui_TableBgTarget_RowBg0(), 0x35404CFF)
      reaper.ImGui_TableHeader(ctx, label)
    end

    if #actions == 0 then
      reaper.ImGui_TableNextRow(ctx)
      reaper.ImGui_TableSetColumnIndex(ctx, 0)
      reaper.ImGui_Text(ctx, "Liste vide. Ajoute une action avec les boutons +.")
    else
      local move_from, move_to
      local delete_row
      local function drag_row(i, a)
        if reaper.ImGui_BeginDragDropSource(ctx) then
          reaper.ImGui_SetDragDropPayload(ctx, "ACTROW", tostring(i))
          local n = 0
          if picked[a.id] then for _ in pairs(picked) do n = n + 1 end end
          reaper.ImGui_Text(ctx, n > 1 and (n.." actions") or a.name)
          reaper.ImGui_EndDragDropSource(ctx)
        end
        if reaper.ImGui_BeginDragDropTarget(ctx) then
          local ok, payload = reaper.ImGui_AcceptDragDropPayload(ctx, "ACTROW")
          if ok then move_from, move_to = tonumber(payload), i end
          reaper.ImGui_EndDragDropTarget(ctx)
        end
      end

      for i, a in ipairs(actions) do
        reaper.ImGui_PushID(ctx, tostring(a.id))
        reaper.ImGui_TableNextRow(ctx)
        reaper.ImGui_TableSetColumnIndex(ctx, 0)
        -- Le numéro ne déclenche JAMAIS la lecture. Il ne fait que désigner
        -- la cue préparée pour GO/clavier ; la sélection multiple se fait
        -- uniquement par clic sur le titre.
        local was_prepared = (selected == a.id)
        local run_state = active_ids[tostring(a.id)]
        if a.type == "stop" and (stop_until[a.id] or 0) > reaper.time_precise() then run_state = "stop" end
        local number_bg = nil
        if run_state == "fade" then
          number_bg = (math.floor(reaper.time_precise()*3) % 2 == 0) and 0xD32F2FFF or 0x7F1D1DFF
        elseif run_state == "run" or run_state == "stop" then
          number_bg = 0xD32F2FFF
        elseif was_prepared then
          -- Vert uniquement pour la cue préparée, indépendamment de la sélection du titre.
          number_bg = 0x45A049FF
        end
        if number_bg then
          reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Header(), number_bg)
          reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_HeaderHovered(), number_bg)
          reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_HeaderActive(), number_bg)
        end
        reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Text(), 0x000000FF)
        if reaper.ImGui_Selectable(ctx, tostring(i) .. "##rownum", was_prepared) then
          local _, del_mod = mods_shift_multi()
          if del_mod then
            delete_row = i -- supprimé après la boucle d'affichage
          else
            selected = a.id
          end
        end
        reaper.ImGui_PopStyleColor(ctx)
        if number_bg then reaper.ImGui_PopStyleColor(ctx, 3) end
        if reaper.ImGui_IsItemHovered(ctx) then
          reaper.ImGui_SetTooltip(ctx, "Cliquer le numéro : préparer la cue, sans la sélectionner ni la déclencher.\nCtrl/Cmd + clic : SUPPRIMER cette ligne.")
        end
        drag_row(i, a)

        reaper.ImGui_TableSetColumnIndex(ctx, 1)
        local title_text = tostring(a.name or "")
        -- Un STOP ciblé affiche les titres des cues cibles, pas leurs IDs.
        -- La saisie/capture des cibles reste basée sur les IDs, qui sont stables.
        if a.type == "stop" then
          local target_ids, seen = {}, {}
          if type(a.targets_text) == "string" and a.targets_text:match("%S") then
            for token in (a.targets_text .. ","):gmatch("(.-),") do
              local digits = token:match("^%s*[Qq]?(%d+)%s*$")
              if digits then
                local id = tonumber(digits)
                if not seen[id] then target_ids[#target_ids+1] = id; seen[id] = true end
              end
            end
          elseif a.targets and #a.targets > 0 then
            for _, id in ipairs(a.targets) do
              id = tonumber(id) or id
              if not seen[id] then target_ids[#target_ids+1] = id; seen[id] = true end
            end
          end
          local target_names = {}
          for _, target_id in ipairs(target_ids) do
            local found_name
            for _, tab in ipairs(tabs or {}) do
              for _, target_action in ipairs(tab.actions or {}) do
                if tostring(target_action.id) == tostring(target_id) and target_action.type == "cue" then
                  found_name = target_action.name or ("Cue " .. tostring(target_id))
                  break
                end
              end
              if found_name then break end
            end
            target_names[#target_names+1] = found_name or ("Cue introuvable " .. tostring(target_id))
          end
          if #target_names > 0 then title_text = "STOP " .. table.concat(target_names, "/") end
        elseif a.type == "pause" or a.type == "devamp" then
          -- Titre automatique : pause "cue x", "cue y" (basé sur les IDs, stables).
          local names = {}
          for _, target_id in ipairs(resolve_targets(a) or {}) do
            local found_name
            for _, tab in ipairs(tabs or {}) do
              for _, target_action in ipairs(tab.actions or {}) do
                if tostring(target_action.id) == tostring(target_id) and target_action.type == "cue" then
                  found_name = target_action.name or ("Cue " .. tostring(target_id))
                  break
                end
              end
              if found_name then break end
            end
            names[#names+1] = '"' .. (found_name or ("Cue introuvable " .. tostring(target_id))) .. '"'
          end
          local verb = a.type == "devamp" and "devamp" or (a.unpause == true and "unpause" or "pause")
          if #names > 0 then title_text = verb .. " " .. table.concat(names, ", ") end
        end
        if reaper.ImGui_Selectable(ctx, title_text .. "##nm", picked[a.id] or false) then
          -- Le clic sur le titre ne change NI la cue préparée NI l'éditeur :
          -- il ne gère que la sélection multiple (captures de cibles).
          -- Sélection Windows : clic simple = remplacer, Ctrl = basculer,
          -- Maj = étendre depuis l'ancre. Ne déclenche jamais la cue.
          local shift, multi = mods_shift_multi()
          if shift then
            local anchor = pick_anchor
            if not anchor or not actions[anchor] then anchor = i end
            pick_range(anchor, i)
          elseif multi then
            if picked[a.id] then picked[a.id] = nil else picked[a.id] = true end
            pick_anchor = i
          else
            -- La sélection du titre ne change pas la cue préparée (selected).
            picked = {[a.id] = true}
            pick_anchor = i
          end
        end
        -- Déposer un fichier audio sur le titre crée une nouvelle cue juste après cette ligne.
        accept_audio_file_drop_create(i)
        if reaper.ImGui_IsItemHovered(ctx) then
          reaper.ImGui_SetTooltip(ctx, "Titre : sélectionner. Ctrl+clic : ajouter/retirer. Maj+clic : sélectionner une plage. Dépose un fichier audio ici pour créer une nouvelle cue Fichier après cette ligne.")
        end

        reaper.ImGui_TableSetColumnIndex(ctx, 2)
        reaper.ImGui_Text(ctx, TYPE_LABEL[a.type] or "?")

        reaper.ImGui_TableSetColumnIndex(ctx, 3)
        local st = a.type == "cue" and active_ids[tostring(a.id)] or nil
        if a.type == "stop" and (stop_until[a.id] or 0) > reaper.time_precise() then st = "stop" end
        local lbl, col = "PREV", nil
        if st == "run" or st == "stop" then
          lbl, col = "RUN", 0xD32F2FFF
        elseif st == "fade" then
          lbl = "RUN"
          col = (math.floor(reaper.time_precise()*3) % 2 == 0) and 0xD32F2FFF or 0x5A1A1AFF
        elseif a.id == selected then
          col = 0x2E8B57FF
        end
        if col then reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Button(), col) end
        if reaper.ImGui_Button(ctx, lbl, S(48), 0) then fire(a) end
        if col then reaper.ImGui_PopStyleColor(ctx) end
        -- Petit STOP individuel dans la colonne Statut : il cible l'ID de cette cue
        -- sans modifier la cue préparée ni la sélection multiple.
        reaper.ImGui_SameLine(ctx, 0, S(3))
        if a.type == "cue" then
          if reaper.ImGui_SmallButton(ctx, "■##stopcue" .. tostring(a.id)) then
            stop_targets({a.id}, stop_fade)
            stop_until[a.id] = reaper.time_precise() + stop_fade + 0.2 + margin/1000
          end
          if reaper.ImGui_IsItemHovered(ctx) then
            reaper.ImGui_SetTooltip(ctx, "STOP uniquement la cue ID " .. tostring(a.id))
          end
        else
          -- Réserver l'espace pour garder l'alignement des boutons de statut.
          reaper.ImGui_Dummy(ctx, S(18), S(1))
        end

        if auto_chain and auto_chain.source_id == a.id and auto_chain.tab_index == active_tab then
          local remaining = math.max(0, auto_chain.deadline - reaper.time_precise())
          reaper.ImGui_Text(ctx, string.format("%s %.1f s", auto_chain.mode == "follow" and "FOLLOW" or "AUTO", remaining))
        end

        -- AUTO et FOLLOW sont exclusifs et disponibles pour toutes les actions,
        -- y compris STOP. DELAY est commun aux deux modes.
        reaper.ImGui_TableSetColumnIndex(ctx, 4)
        local changed_auto, new_auto = reaper.ImGui_Checkbox(ctx, "##auto_row_" .. tostring(a.id), a.auto == true)
        if changed_auto then
          a.auto = new_auto
          if new_auto then a.follow = false end
          save()
        end
        if reaper.ImGui_IsItemHovered(ctx) then
          reaper.ImGui_SetTooltip(ctx, "AUTO : lance la cue suivante après DELAY à partir du déclenchement.")
        end

        reaper.ImGui_TableSetColumnIndex(ctx, 5)
        local changed_follow, new_follow = reaper.ImGui_Checkbox(ctx, "##follow_row_" .. tostring(a.id), a.follow == true)
        if changed_follow then
          a.follow = new_follow
          if new_follow then a.auto = false end
          save()
        end
        if reaper.ImGui_IsItemHovered(ctx) then
          reaper.ImGui_SetTooltip(ctx, "FOLLOW : attend la fin de l'action, puis DELAY, avant la cue suivante.")
        end

        reaper.ImGui_TableSetColumnIndex(ctx, 6)
        reaper.ImGui_SetNextItemWidth(ctx, -1)
        local changed_delay, new_delay = reaper.ImGui_InputDouble(ctx, "##delay_row_" .. tostring(a.id), tonumber(a.delay) or 0, 0, 0, "%.2f")
        if changed_delay then a.delay = math.max(0, new_delay); save() end
        if reaper.ImGui_IsItemHovered(ctx) then
          reaper.ImGui_SetTooltip(ctx, "DELAY en secondes, utilisé par AUTO ou FOLLOW.")
        end

        reaper.ImGui_TableSetColumnIndex(ctx, 7)
        local tr = find_track(a.track)
        local cible = tr and track_name(tr) or (a.type == "cue" and (a.src == "file" and "(choisir)" or "(origine)") or "-")
        if a.type == "preset" then
          ensure_snap(a)
          cible = a.snap and (#a.snap.order.." piste(s)") or "-"
        elseif a.type == "stop" or a.type == "pause" or a.type == "devamp" then
          local ids = resolve_targets(a)
          cible = ids and (#ids.." cue(s)") or "toutes"
        elseif a.type == "osc" then
          cible = a.port_name ~= "" and a.port_name or "(port)"
        elseif a.type == "midi" then
          cible = tr and track_name(tr) or "(piste)"
        end
        reaper.ImGui_Text(ctx, cible)

        reaper.ImGui_TableSetColumnIndex(ctx, 8)
        reaper.ImGui_Text(ctx, tostring(a.id or "?"))
        reaper.ImGui_PopID(ctx)
      end
      if move_from and move_to then move_rows(move_from, move_to) end
      if delete_row and actions[delete_row] then
        local da = actions[delete_row]
        picked[da.id] = nil
        table.remove(actions, delete_row)
        if selected == da.id then
          local nxt = actions[math.min(delete_row, #actions)]
          if nxt then pick_only(nxt, math.min(delete_row, #actions))
          else selected, pick_anchor = nil, nil end
        end
        sel_i = nil
        for k, x in ipairs(actions) do if x.id == selected then sel_i = k; break end end
        save()
        status = "Action supprimée : " .. tostring(da.name or da.id)
      end
    end
    reaper.ImGui_EndTable(ctx)
  end

  -- Cible de dépôt au niveau du tableau lui-même (pas de case dédiée).
  -- Les titres restent des cibles prioritaires pour insérer après une cue ;
  -- déposer sur le tableau hors d'un titre ajoute à la fin.
  accept_audio_file_drop_create(#actions)

  local y_lower = reaper.ImGui_GetCursorPosY(ctx)
  local selected_ids = {}
  for _, tab in ipairs(tabs or {}) do
    for _, x in ipairs(tab.actions or {}) do
      if picked[x.id] then selected_ids[#selected_ids+1] = "Q"..tostring(x.id) end
    end
  end
  if #selected_ids > 0 then
    reaper.ImGui_Text(ctx, "Sélection globale : " .. table.concat(selected_ids, ", "))
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_SmallButton(ctx, "Vider la sélection") then picked, pick_anchor = {}, nil end
  end

  -- Séparateur redimensionnable : glisser la poignée pour donner plus ou moins
  -- de hauteur au panneau de paramètres (et donc à la liste des cues).
  local sep_w = select(1, reaper.ImGui_GetContentRegionAvail(ctx))
  local sep_x, sep_y = reaper.ImGui_GetCursorScreenPos(ctx)
  reaper.ImGui_InvisibleButton(ctx, "##resize_action_editor", sep_w, S(12))
  local sep_hover = reaper.ImGui_IsItemHovered(ctx)
  local sep_active = reaper.ImGui_IsItemActive(ctx)
  if sep_hover or sep_active then
    if reaper.ImGui_SetMouseCursor and reaper.ImGui_MouseCursor_ResizeNS then
      reaper.ImGui_SetMouseCursor(ctx, reaper.ImGui_MouseCursor_ResizeNS())
    end
  end
  if sep_active and reaper.ImGui_IsMouseDown(ctx, C_LEFT) then
    local _, mouse_y = reaper.ImGui_GetMousePos(ctx)
    local _, window_y = reaper.ImGui_GetWindowPos(ctx)
    local _, window_h = reaper.ImGui_GetWindowSize(ctx)
    -- mouse_y indique la limite supérieure du panneau inférieur.
    lower_h_override = math.max(S(110), math.min(window_h - S(160), window_y + window_h - mouse_y))
  end
  local sep_dl = reaper.ImGui_GetWindowDrawList(ctx)
  local sep_col = sep_active and 0x4FA3D1FF or (sep_hover and 0x7FA8C8FF or 0x606060FF)
  reaper.ImGui_DrawList_AddRectFilled(sep_dl, sep_x, sep_y, sep_x + sep_w, sep_y + S(12),
    (sep_hover or sep_active) and 0x303B46FF or 0x252525FF)
  reaper.ImGui_DrawList_AddLine(sep_dl, sep_x, sep_y + S(6), sep_x + sep_w, sep_y + S(6), sep_col, S(2))
  reaper.ImGui_DrawList_AddText(sep_dl, sep_x + sep_w * 0.5 - S(18), sep_y, sep_col, "⋮⋮")

  if sel_i then
    local open_ed = reaper.ImGui_CollapsingHeader(ctx, "Paramètres de l'action sélectionnée##edhdr", nil, reaper.ImGui_TreeNodeFlags_DefaultOpen())
    if open_ed then draw_editor(actions[sel_i], sel_i) end
  end

  reaper.ImGui_Separator(ctx)
  reaper.ImGui_Text(ctx, status)
  lower_h = reaper.ImGui_GetCursorPosY(ctx) - y_lower
end

---------------------------------------------------------------- Boucle principale
local function loop()
  process_jobs()
  poll_midi_note_offs()
  process_auto_chain()
  reaper.ImGui_SetNextWindowSize(ctx, 720, 820, reaper.ImGui_Cond_FirstUseEver())
  local visible, open = reaper.ImGui_Begin(ctx, "Actions##v2", true)
  if visible then
    if reaper.ImGui_SetWindowFontScale then reaper.ImGui_SetWindowFontScale(ctx, ui_scale) end
    draw()
    reaper.ImGui_End(ctx)
  end
  if open then reaper.defer(loop) end
end

load_data()
history_last = current_data_string()
reaper.defer(loop)
