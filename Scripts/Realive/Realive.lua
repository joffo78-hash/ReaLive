-- @description Realive — système de cues pour REAPER
-- @version 1.5.4
-- @author joffo78-hash
-- @link https://github.com/joffo78-hash/Realive
-- @donation https://buymeacoffee.com/joffo
-- @changelog Ajout du lien pour soutenir le projet via Buy Me a Coffee.
-- @about
--   Realive est un système de cues de type QLab pour REAPER.
--   Nécessite ReaImGui. Les fonctions OSC nécessitent Mavriq Lua Sockets.
--
-- ActionList.lua
-- Playlist d'actions type QLab pour REAPER (ReaImGui)
-- Types : AUDIO (fichier), REGION, STOP, SNAPSHOT, OSC, MIDI

if not reaper.ImGui_CreateContext then
  reaper.MB("ReaImGui n'est pas installé.\nInstallez-le via ReaPack.", "ActionList", 0)
  return
end

-- Fenêtre volontairement non dockable : elle s'ouvre comme fenêtre flottante.
-- Ne pas activer ImGui_ConfigFlags_DockingEnable ici.
local ctx = reaper.ImGui_CreateContext("Actions")

-- Table d'API : déclarée tôt pour que function X.* soit valide au chargement.
local X = {} -- aides regroupées (limite Lua : 200 variables locales)

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
  local base = resource .. "/Scripts/Mavriq ReaScript Repository/Various/"
  local roots = {
    base .. "Mavriq-Lua-Sockets",
    base .. "Mavriq Lua Sockets",
    base .. "Mavriq lua sockets",
    base .. "Mavriq Lua Sockets 1.2",
    resource .. "/Scripts/Mavriq-Lua-Sockets",
    resource .. "/Scripts/Mavriq Lua Sockets",
  }

  -- Les modules natifs n'ont pas la même extension selon le système :
  -- Windows .dll ; macOS/Linux .so (certaines distributions utilisent .dylib).
  local binary_names = {"socket/core.dll", "socket/core.so", "socket/core.dylib"}
  local socket_root, socket_binary
  for _, root in ipairs(roots) do
    for _, binary in ipairs(binary_names) do
      local f = io.open(root .. "/" .. binary, "rb")
      if f then
        f:close()
        socket_root, socket_binary = root, binary
        break
      end
    end
    if socket_root then break end
  end

  if socket_root then
    -- require("socket.core") transforme le point en séparateur de dossier :
    -- le motif /?.so permet donc de trouver /socket/core.so sur macOS.
    local ext = socket_binary:match("%.([^%.]+)$")
    package.cpath = socket_root .. "/?." .. ext .. ";" .. package.cpath
    package.path = socket_root .. "/?.lua;" ..
                   socket_root .. "/?/init.lua;" .. package.path

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
      socket_init_status = "OSC désactivé : Mavriq Lua Sockets a été trouvé, mais socket.core n'a pas pu être chargé. Vérifier que la version installée correspond à REAPER et au système."
      if not ok then
        socket_init_status = socket_init_status .. " Détail Lua : " .. tostring(sock)
      end
    end
  else
    socket_init_status = "OSC désactivé : fichier natif LuaSocket introuvable. Installer Mavriq Lua Sockets 1.2 via ReaPack."
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
function X.sync_active_tab()
  if not tabs or #tabs == 0 then tabs = {{name = "Liste 1", actions = {}}} end
  active_tab = math.max(1, math.min(active_tab or 1, #tabs))
  actions = tabs[active_tab].actions
end
function X.new_tab_name()
  return "Liste " .. tostring(#tabs + 1)
end
function X.clone_table(value)
  if type(value) ~= "table" then return value end
  local out = {}
  for k, v in pairs(value) do out[X.clone_table(k)] = X.clone_table(v) end
  return out
end
local selected = nil -- cue préparée pour GO/clavier
local picked, pick_anchor = {}, nil
local status = has_socket and "Prêt (OSC disponible)." or ("Prêt. " .. socket_init_status)
local file_drop_api_warning_shown = false
local margin = tonumber(reaper.GetExtState(EXT, "margin")) or 200
local fades, morphs = {}, {}
local del_jobs = {}
local HOLD = 1.0
local ui_scale = tonumber(reaper.GetExtState(EXT, "zoom")) or 1.0
local lower_h_override = nil

function X.S(x) return math.floor(x * ui_scale + 0.5) end
function X.set_zoom(z)
  ui_scale = math.max(0.6, math.min(2.5, z))
  reaper.SetExtState(EXT, "zoom", string.format("%.3f", ui_scale), true)
end

-- Couleur de fond de l'interface : le niveau 0 conserve le thème REAPER actuel.
-- Le curseur va progressivement vers le blanc ; hue/saturation teintent les gris.
local prefs
function X.unpack_rgba(col)
  col = math.floor(tonumber(col) or 0x3B82F6FF)
  return (col >> 24) & 0xFF, (col >> 16) & 0xFF, (col >> 8) & 0xFF
end
function X.pack_rgba(r, g, b)
  r = math.max(0, math.min(255, math.floor(r + 0.5)))
  g = math.max(0, math.min(255, math.floor(g + 0.5)))
  b = math.max(0, math.min(255, math.floor(b + 0.5)))
  return (r << 24) | (g << 16) | (b << 8) | 0xFF
end
function X.interface_bg_color()
  local level = math.max(0, math.min(1, tonumber(prefs.bg_level) or 0))
  if level <= 0.0001 then return nil end -- garde exactement le fond actuel
  local gray = 32 + level * 223
  local r, g, b = gray, gray, gray
  local hr, hg, hb = X.unpack_rgba(prefs.bg_hue or 0x3B82F6FF)
  local sat = math.max(0, math.min(1, tonumber(prefs.bg_saturation) or 0))
  -- La teinte est la plus visible dans les gris et s'efface à l'approche du blanc.
  local mix = sat * (1 - level)
  r = r * (1 - mix) + hr * mix
  g = g * (1 - mix) + hg * mix
  b = b * (1 - mix) + hb * mix
  return X.pack_rgba(r, g, b)
end

-- Couleur d'accent utilisée pour les éléments bleus de l'interface.
function X.accent_color()
  local r, g, b = X.unpack_rgba(prefs.accent_hue or 0x3B82F6FF)
  local sat = math.max(0, math.min(1, tonumber(prefs.accent_saturation) or 1))
  local gray = (r + g + b) / 3
  r, g, b = gray + (r - gray) * sat, gray + (g - gray) * sat, gray + (b - gray) * sat
  return X.pack_rgba(r, g, b)
end

function X.accent_variant(col, amount)
  local r, g, b = X.unpack_rgba(col)
  if amount >= 0 then
    r, g, b = r + (255-r)*amount, g + (255-g)*amount, b + (255-b)*amount
  else
    local f = 1 + amount
    r, g, b = r*f, g*f, b*f
  end
  return X.pack_rgba(r, g, b)
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
-- Horloge jusqu'à laquelle un fondu STOP est en cours (ne pas stopper le transport).
local fade_hold_until = 0
-- Enchaînement automatique : compte à rebours de la cue source vers la suivante.
local auto_chain = nil
local ext_runs = {}
local ANTICLICK = 0.003 -- protection anti-clic minimale, sans délai ajouté
local stop_fade = tonumber(reaper.GetExtState(EXT, "stopfade")) or 1.0
local stop_curve = tonumber(reaper.GetExtState(EXT, "stopcurve")) or 0.5

prefs = {
  auto_stop       = false,
  delete_on_stop  = true,
  exclusive_track = true,
  bg_level        = 0,
  bg_hue          = 0x3B82F6FF,
  bg_saturation   = 0,
  accent_hue      = 0x3B82F6FF,
  accent_saturation = 1,
  ports           = {},
}

local cue_session, np_since, last_scan, idle_since = false, nil, 0, nil
-- Position d'origine de la session (curseur d'édition au moment du GO).
-- Sur STOP avec Delete on stop, la tête de lecture y revient.
local session_origin = nil
local actions_by_id = {}
-- (X.apply_snap assigné plus bas)
-- (X.fire assigné plus bas)
-- (X.default_track_guid assigné plus bas)
-- (X.delete_cuelist_items assigné plus bas)
-- (X.delete_all_cuelist_items assigné plus bas)

local item_props = {"D_LENGTH","D_VOL","D_FADEINLEN","D_FADEOUTLEN","D_FADEINSHAPE","D_FADEOUTSHAPE","D_SNAPOFFSET"}
local take_props = {"D_STARTOFFS","D_VOL","D_PAN","D_PLAYRATE","D_PITCH"}

---------------------------------------------------------------- Sérialisation
function X.ser(v)
  local t = type(v)
  if t == "table" then
    local parts = {}
    for k, x in pairs(v) do parts[#parts+1] = "["..X.ser(k).."]="..X.ser(x) end
    return "{"..table.concat(parts,",").."}"
  elseif t == "string" then return string.format("%q", v)
  elseif t == "number" then return string.format("%.17g", v)
  else return tostring(v) end
end

function X.rebuild_id_map()
  if tabs and tabs[active_tab] and actions then tabs[active_tab].actions = actions end
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

function X.current_data_string()
  if tabs and tabs[active_tab] and actions then tabs[active_tab].actions = actions end
  return X.ser({ actions = actions, tabs = tabs, active_tab = active_tab, next_id = next_id, prefs = prefs })
end

function X.save()
  local data = X.current_data_string()
  if not history_restoring and history_last and data ~= history_last then
    undo_stack[#undo_stack + 1] = history_last
    if #undo_stack > HISTORY_LIMIT then table.remove(undo_stack, 1) end
    redo_stack = {}
  end
  reaper.SetProjExtState(PROJ, EXT, "data", data)
  history_last = data
  X.rebuild_id_map()
end

function X.restore_history_state(data)
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
    if type(d.actions) == "table" and tabs[active_tab] then tabs[active_tab].actions = d.actions end
    X.sync_active_tab()
  else
    actions = d.actions or {}
    tabs = {{name = "Liste 1", actions = actions}}
    active_tab = 1
    X.sync_active_tab()
  end
  if type(d.prefs) == "table" then
    for k, v in pairs(d.prefs) do prefs[k] = v end
  end
  prefs.ports = prefs.ports or {}
  X.rebuild_id_map()
  local encoded = X.current_data_string()
  reaper.SetProjExtState(PROJ, EXT, "data", encoded)
  history_last = encoded
  history_restoring = false
  picked, pick_anchor, selected = {}, nil, nil
  return true
end

function X.undo_change()
  if #undo_stack == 0 then status = "Rien à annuler."; return end
  redo_stack[#redo_stack + 1] = X.current_data_string()
  local previous = table.remove(undo_stack)
  if X.restore_history_state(previous) then status = "Modification annulée." end
end

function X.redo_change()
  if #redo_stack == 0 then status = "Rien à rétablir."; return end
  undo_stack[#undo_stack + 1] = X.current_data_string()
  local following = table.remove(redo_stack)
  if X.restore_history_state(following) then status = "Modification rétablie." end
end

function X.load_data()
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
          if type(d.actions) == "table" and tabs[active_tab] then tabs[active_tab].actions = d.actions end
          X.sync_active_tab()
        else
          actions = d.actions or {}
          tabs = {{name = "Liste 1", actions = actions}}
          active_tab = 1
          X.sync_active_tab()
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
  for _, tab in ipairs(tabs or {}) do
    for _, act in ipairs(tab.actions or {}) do X.normalize_action(act) end
  end
  X.rebuild_id_map()
end

---------------------------------------------------------------- Utilitaires
function X.is_playing()
  return (math.floor(reaper.GetPlayStateEx(PROJ)) & 1) ~= 0
end

function X.now_pos()
  return X.is_playing() and reaper.GetPlayPosition2Ex(PROJ) or reaper.GetCursorPositionEx(PROJ)
end

-- Timeline à jour ≠ audio à jour : REAPER précharge le média. Un seek play
-- à la position courante force le moteur à reconstruire à partir des items actuels.
function X.resync_play_engine()
  if not X.is_playing() then return end
  local p = reaper.GetPlayPosition2Ex(PROJ)
  reaper.SetEditCurPos2(PROJ, p, false, true)
end

function X.track_name(tr)
  local _, n = reaper.GetTrackName(tr)
  return n
end

-- Recherche d'une piste par GUID, dans le projet courant par défaut.
-- `proj` optionnel : permet de retrouver une piste dans un autre onglet
-- (utilisé par les snapshots liés / autonomes qui peuvent cibler un autre projet).
function X.find_track(guid, proj)
  if not guid then return nil end
  proj = proj or PROJ
  for i = 0, reaper.CountTracks(proj)-1 do
    local t = reaper.GetTrack(proj, i)
    if reaper.GetTrackGUID(t) == guid then return t end
  end
end

function X.tracks_of(tr)
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

function X.get_regions(proj)
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

function X.find_track_by_name(name)
  for i = 0, reaper.CountTracks(PROJ)-1 do
    local t = reaper.GetTrack(PROJ, i)
    if X.track_name(t) == name then return t end
  end
end

-- Nom d'affichage d'un projet (évite une locale de plus : limite Lua 200).
function X.project_label(proj)
  proj = proj or PROJ
  local fn = ""
  local i = 0
  while true do
    local p, path = reaper.EnumProjects(i)
    if not p then break end
    if p == proj then fn = path or ""; break end
    i = i + 1
  end
  if fn ~= "" then
    return fn:match("([^/\\]+)$") or fn
  end
  if reaper.GetProjectName then
    local name = reaper.GetProjectName(proj, "")
    if name and name ~= "" then return name end
  end
  return "(sans nom)"
end

function X.other_projects()
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

function X.find_project(fn)
  if not fn or fn == "" then return PROJ end
  for _, o in ipairs(X.other_projects()) do
    if o.fn == fn then return o.proj end
  end
  return nil
end

function X.lerp_db(a, b, p)
  if a > 1e-4 and b > 1e-4 then
    local da = 20 * math.log(a, 10)
    local db = 20 * math.log(b, 10)
    return 10 ^ ((da + (db-da)*p) / 20)
  end
  return a + (b-a)*p
end

function X.on_main(fn)
  local prev = reaper.EnumProjects(-1)
  if prev ~= PROJ then
    reaper.SelectProjectInstance(PROJ)
    fn()
    reaper.SelectProjectInstance(prev)
  else
    fn()
  end
end

function X.play_main()
  -- Mémoriser le point de départ avant de lancer la lecture.
  if not X.is_playing() then
    session_origin = reaper.GetCursorPositionEx(PROJ)
  end
  X.on_main(function() reaper.OnPlayButton() end)
  play_check = reaper.time_precise() + 0.5
end

function X.with_proj(p, fn)
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
function X.stop_here()
  local pos = session_origin
  if pos == nil then pos = reaper.GetCursorPositionEx(PROJ) end
  X.on_main(function()
    if (math.floor(reaper.GetPlayStateEx(PROJ)) & 1) ~= 0 then
      reaper.OnPauseButton()
    end
    reaper.SetEditCurPos2(PROJ, pos, true, false)
    reaper.OnStopButton()
  end)
end

function X.active_cue_items()
  local p = X.now_pos()
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
function X.env_gain(env, t)
  local n = env and #env or 0
  if n == 0 then return 1 end
  if t <= env[1].t then return env[1].g end
  if t >= env[n].t then return env[n].g end
  for i = 1, n-1 do
    local p, q = env[i], env[i+1]
    if t <= q.t then
      return X.lerp_db(p.g, q.g, (t - p.t) / math.max(1e-9, q.t - p.t))
    end
  end
  return 1
end

-- Volume (linéaire) d'un item de cue à l'instant source t :
-- enveloppe × gain de la cue (dB lu EN DIRECT, donc cohérent quand on bouge le réglage).
function X.cue_vol(id, env, t)
  local cue = actions_by_id[id] or actions_by_id[tostring(id)]
  local db = cue and tonumber(cue.wave_gain_db) or 0
  local e = (env and #env > 0) and X.env_gain(env, t) or 1
  return e * (10 ^ (db / 20))
end

function X.kill_runs(ids)
  if not ids then
    for _, r in pairs(runs) do r.alive = false end
    return
  end
  local function kill_one(id)
    if id == nil then return end
    if runs[id] then runs[id].alive = false end
    local s = tostring(id)
    if runs[s] then runs[s].alive = false end
    local n = tonumber(id)
    if n ~= nil and runs[n] then runs[n].alive = false end
  end
  if type(ids) == "table" and ids[1] == nil and next(ids) ~= nil then
    -- set-like { [id]=true, ... }
    for id in pairs(ids) do kill_one(id) end
  else
    for _, id in ipairs(ids) do kill_one(id) end
  end
end

-- STOP + fade : les boucles restent vivantes jusqu'à fade_out_end (volume ↓).
function X.begin_run_fades(ids, t_start, t_end)
  local function arm_one(id, r)
    if not r or not r.alive then return end
    if r.loop then
      r.fade_out_start = t_start
      r.fade_out_end = t_end
      r.fade_base_vol = r.fade_base_vol or 1
    else
      r.alive = false
    end
  end
  if not ids then
    for id, r in pairs(runs) do arm_one(id, r) end
    return
  end
  if type(ids) == "table" and ids[1] == nil and next(ids) ~= nil then
    for id in pairs(ids) do
      arm_one(id, runs[id] or runs[tostring(id)] or (tonumber(id) and runs[tonumber(id)]))
    end
  else
    for _, id in ipairs(ids) do
      arm_one(id, runs[id] or runs[tostring(id)] or (tonumber(id) and runs[tonumber(id)]))
    end
  end
end

function X.is_loop_fading_id(id)
  local r = runs[id] or runs[tostring(id)] or (tonumber(id) and runs[tonumber(id)])
  return r and r.alive and r.loop and r.fade_out_end ~= nil
end

-- Récupère un BPM source explicite (métadonnées REAPER, ou nom de fichier du type "120bpm").
-- Sans BPM source connu, il est impossible de calculer un étirement musical fiable.
function X.source_bpm(file)
  if type(file) ~= "string" or file == "" then return nil end
  local src = reaper.PCM_Source_CreateFromFile(file)
  if src then
    if reaper.GetMediaFileMetadata then
      local _, ids = reaper.GetMediaFileMetadata(src, "")
      for key in tostring(ids or ""):gmatch("[^\r\n]+") do
        local lk = key:lower()
        if lk:find("bpm", 1, true) or lk:find("tempo", 1, true) then
          local _, value = reaper.GetMediaFileMetadata(src, key)
          local n = tonumber(tostring(value or ""):match("[%d%.]+"))
          if n and n >= 20 and n <= 400 then
            reaper.PCM_Source_Destroy(src)
            return n
          end
        end
      end
    end
    reaper.PCM_Source_Destroy(src)
  end
  local base = file:match("([^/\\]+)$") or file
  local n = base:lower():match("(%d+%.?%d*)%s*bpm")
  n = tonumber(n)
  if n and n >= 20 and n <= 400 then return n end
  return nil
end

function X.cue_effective_speed(a, pos)
  local speed = math.max(0.01, math.min(16, tonumber(a and a.wave_speed) or 1))
  if not (a and a.wave_stretch_tempo) then return speed, 1 end
  local src_bpm = X.source_bpm(a.file)
  if not src_bpm then return speed, 1 end
  local project_bpm
  if reaper.TimeMap2_GetDividedBpmAtTime then
    project_bpm = reaper.TimeMap2_GetDividedBpmAtTime(PROJ, tonumber(pos) or X.now_pos())
  end
  if not project_bpm or project_bpm <= 0 then
    project_bpm = select(1, reaper.GetProjectTimeSignature2(PROJ))
  end
  if not project_bpm or project_bpm <= 0 then return speed, 1 end
  local ratio = math.max(0.25, math.min(4, project_bpm / src_bpm))
  return math.max(0.01, math.min(16, speed * ratio)), ratio
end

function X.add_file_item(dest, file, pos, tin, seg, fadein, gain, id, markers)
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
  local tempo_ratio = 1
  if cue then
    local db = tonumber(cue.wave_gain_db) or 0
    reaper.SetMediaItemTakeInfo_Value(ntk, "D_VOL", (gain or 1) * (10 ^ (db / 20)))
    reaper.SetMediaItemTakeInfo_Value(ntk, "D_PAN", math.max(-1, math.min(1, tonumber(cue.wave_pan) or 0)))
    speed, tempo_ratio = X.cue_effective_speed(cue, pos)
    reaper.SetMediaItemTakeInfo_Value(ntk, "D_PLAYRATE", speed)
    -- Le tempo est appliqué par un ratio de lecture calculé depuis le BPM source.
    -- On évite C_AUTOSTRETCH sur les items de lecture temps réel : sans BPM source,
    -- REAPER peut produire un étirement invalide sur ces items courts/recoupés.
    reaper.SetMediaItemTakeInfo_Value(ntk, "B_PPITCH", (cue.wave_stretch_tempo and tempo_ratio ~= 1) and 1 or 0)
    local pitch = tonumber(cue.wave_pitch) or 0
    if cue.wave_pitch_link then pitch = 12 * (math.log(speed) / math.log(2)) end
    reaper.SetMediaItemTakeInfo_Value(ntk, "D_PITCH", pitch)
    -- L'inversion est portée par la source SECTION native de REAPER.
    if X.set_item_reverse then X.set_item_reverse(new, cue.wave_reverse) end
    -- L'adaptation initiale est calculée explicitement depuis le BPM source ;
    -- ne pas activer C_AUTOSTRETCH sur les items internes de ReaLive.
    reaper.SetMediaItemInfo_Value(new, "C_BEATATTACHMODE", 0)
    reaper.SetMediaItemInfo_Value(new, "C_AUTOSTRETCH", 0)
  end
  local proj_len = math.max(0.001, (tonumber(seg) or 0) / speed)
  reaper.SetMediaItemInfo_Value(new, "D_POSITION", pos)
  reaper.SetMediaItemInfo_Value(new, "D_LENGTH", proj_len)
  reaper.SetMediaItemInfo_Value(new, "D_FADEINLEN", math.min(fadein or 0, proj_len))
  reaper.SetMediaItemInfo_Value(new, "D_FADEOUTLEN", 0)
  -- Courbe native REAPER : 0 linéaire, valeurs croissantes = formes plus marquées.
  local curve_shape = math.max(0, math.min(6, math.floor((tonumber(cue and cue.fade_curve) or 0) * 6 + 0.5)))
  reaper.SetMediaItemInfo_Value(new, "D_FADEINSHAPE", curve_shape)
  reaper.SetMediaItemInfo_Value(new, "D_FADEOUTSHAPE", curve_shape)
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

function X.copy_take_markers(src_take, dst_take)
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

function X.refresh_active(now)
  if now - last_active_scan < 0.12 then return end
  last_active_scan = now
  local set = {}
  if X.is_playing() then
    local p = X.now_pos()
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
  -- Source de vérité runtime : les runs (indispensable pour les boucles,
  -- y compris pendant un STOP+fade où le volume descend sans D_FADEOUTLEN).
  for id, r in pairs(runs) do
    if r and r.alive then
      local key = tostring(id)
      if r.fade_out_end then
        set[key] = "fade"
      elseif not r.paused then
        if set[key] ~= "fade" then set[key] = "run" end
      end
    end
  end
  for id, r in pairs(ext_runs) do
    set[tostring(id)] = r.stopping and "fade" or "run"
  end
  active_ids = set
end

-- Items audio (hors keepalive MIDI) d'une cue sur sa piste.
function X.cue_audio_items(dest, id, fn)
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

-- Piste technique discrète : les items MIDI silencieux maintiennent le transport
-- actif, sans recouvrir visuellement les cues de l'utilisateur.
function X.keepalive_track()
  local tr = nil
  for i = 0, reaper.CountTracks(PROJ) - 1 do
    local t = reaper.GetTrack(PROJ, i)
    local _, flag = reaper.GetSetMediaTrackInfo_String(t, "P_EXT:cuelist_internal_keepalive", "", false)
    if flag == "1" then tr = t; break end
  end
  if not tr then
    local n = reaper.CountTracks(PROJ)
    reaper.InsertTrackAtIndex(n, true)
    tr = reaper.GetTrack(PROJ, n)
    if tr then
      reaper.GetSetMediaTrackInfo_String(tr, "P_NAME", "ReaLive — interne (transport)", true)
      reaper.GetSetMediaTrackInfo_String(tr, "P_EXT:cuelist_internal_keepalive", "1", true)
      reaper.SetMediaTrackInfo_Value(tr, "B_SHOWINMIXER", 0)
      reaper.SetMediaTrackInfo_Value(tr, "I_HEIGHTOVERRIDE", 1)
      reaper.TrackList_AdjustWindows(false)
    end
  end
  return tr
end

-- Supprime les items "keepalive" (MIDI vides posés pendant une pause ou une boucle).
function X.remove_keepalive(id)
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
function X.run_source_time(r, p)
  if not r then return nil end
  local speed = math.max(0.01, r.speed or 1)
  if r.paused and r.pause_src and (not r.pause_proj or p >= r.pause_proj) then return r.pause_src end
  local dest = X.find_track(r.dest_guid)
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
function X.schedule_release(r, dest, at)
  local speed = math.max(0.01, r.speed or 1)
  local lo, tout = r.lo, r.tout
  local rel_seg = math.max(0, tout - lo)
  if rel_seg > 0.005 then
    local gain = (r.env and #r.env > 0) and X.env_gain(r.env, lo) or 1
    X.add_file_item(dest, r.file, at, lo, rel_seg, 0, gain, r.id, r.markers)
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
function X.replan_loop_run(a, r)
  if not (r and r.loop and r.alive and not r.paused) then return end
  local dest = X.find_track(r.dest_guid)
  if not dest then return end
  local old_lo = r.lo
  r.tin, r.tout = a.inpt, a.outpt
  r.li = math.max(r.tin, math.min(tonumber(a.loop_in) or r.tin, r.tout - 0.01))
  r.lo = math.max(r.li + 0.01, math.min(tonumber(a.loop_out) or r.tout, r.tout))
  r.seg = r.lo - r.li
  r.speed = X.cue_effective_speed(a, X.now_pos())
  r.env = a.env or r.env or {}
  r.markers = a.markers or r.markers or {}
  local speed = r.speed
  local p = X.now_pos()
  local cur, cur_pos, cur_so
  local future = {}
  X.cue_audio_items(dest, r.id, function(it, tk)
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
      X.schedule_release(r, dest, r.next)
    end
  else
    r.next = p + margin / 1000
    if r.phase == "release" then X.schedule_release(r, dest, r.next) end
  end
  -- gains (enveloppe + gain de cue) sur les items conservés
  local db = tonumber(a.wave_gain_db) or 0
  X.cue_audio_items(dest, r.id, function(it, tk)
    local so = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS")
    local g = (r.env and #r.env > 0) and X.env_gain(r.env, so) or 1
    reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", g * (10 ^ (db / 20)))
    reaper.UpdateItemInProject(it)
  end)
  reaper.UpdateArrange()
end

-- Résout la liste d'IDs ciblés d'une action (Q1,Q8…). nil = toutes les cues.
function X.resolve_targets(a)
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
function X.pause_run(id, fade)
  local r = runs[id]
  if not r or not r.alive or r.paused then return false end
  local dest = X.find_track(r.dest_guid)
  local p = X.now_pos()
  local F = math.max(0, math.min(PAUSE_FADE_MAX, tonumber(fade) or 0))
  local t_end, src_end = p + F, nil
  if F > 0 then
    X.cue_audio_items(dest, id, function(it, tk)
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
  if not src_end then src_end = X.run_source_time(r, p) or r.tin end
  r.paused = true
  r.pause_src = src_end
  r.pause_proj = t_end
  if dest then
    local to_del, to_cut = {}, {}
    local lo_ref = r.lo or r.tout
    X.cue_audio_items(dest, id, function(it, tk)
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
    X.remove_keepalive(id)
    local ka_track = X.keepalive_track()
    local ka = ka_track and reaper.CreateNewMIDIItemInProj(ka_track, t_end, t_end + 3600, false)
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
function X.resume_run(id, fade)
  local r = runs[id]
  if not r or not r.alive or not r.paused then return false end
  local dest = X.find_track(r.dest_guid)
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
  local was_playing = X.is_playing()
  -- Ne pas chevaucher un fade de pause encore en cours.
  local place = math.max(X.now_pos() + margin/1000, tonumber(r.pause_proj) or 0)
  X.remove_keepalive(id)
  if dest then
    local gain = (r.env and #r.env > 0) and X.env_gain(r.env, src) or 1
    local fi = math.max(0, tonumber(fade) or 0)
    X.add_file_item(dest, r.file, place, src, seg, math.min(fi, seg / speed), gain, id, r.markers)
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
-- next_id optionnel : après la fin du cycle (région) / release (fichier), déclencher cette cue.

function X.clear_devamp_state(id)
  if id == nil then return end
  devamp_flags[id] = nil
  devamp_flags[tostring(id)] = nil
  local r = runs[id] or runs[tostring(id)]
  if r then
    r.devamp = false
    r.devamp_armed = false
    r.devamp_next = nil
  end
  local er = ext_runs[id] or ext_runs[tostring(id)]
  if er then
    er.devamp = false
    er.devamp_armed = false
    er.devamp_next = nil
  end
end

function X.devamp_run(id, next_id, crossfade)
  next_id = next_id and tonumber(next_id) or nil
  crossfade = math.max(0, tonumber(crossfade) or 0)
  local r = runs[id]
  if r and r.alive and r.loop then
    if not (r.phase == "release" or r.devamp or r.devamp_armed) then
      r.devamp = true
      r.devamp_armed = false
      r.devamp_next = next_id
      r.devamp_crossfade = r.region_loop and crossfade or 0
      r.devamp_transition_started = false
      devamp_flags[id] = true
      devamp_flags[tostring(id)] = true
      if r.region_loop then
        status = string.format("Devamp armé (Q%s) : fin du cycle région%s.",
          tostring(id), next_id and (" → Q"..tostring(next_id)) or ", puis arrêt")
      else
        status = string.format("Devamp armé (Q%s) : fin du passage jusqu'à Lo, puis OUT%s.",
          tostring(id), next_id and (" → Q"..tostring(next_id)) or "")
      end
      return true
    end
    return false
  end
  local er = ext_runs[id] or ext_runs[tostring(id)]
  if er and er.loop and not (er.devamp or er.devamp_armed) then
    er.devamp = true
    er.devamp_next = next_id
    er.devamp_crossfade = crossfade
    er.devamp_transition_started = false
    devamp_flags[id] = true
    devamp_flags[tostring(id)] = true
    status = string.format("Devamp armé (Q%s) : fin du cycle région%s.",
      tostring(id), next_id and (" → Q"..tostring(next_id)) or ", puis arrêt")
    return true
  end
  return false
end

function X.resolve_devamp_next(a)
  if not a then return nil end
  if a.devamp_to then
    local n = tonumber(a.devamp_to)
    if n then return n end
  end
  local tx = a.devamp_to_text
  if type(tx) == "string" and tx:match("%S") then
    local digits = tx:match("^[Qq]?(%d+)$")
    if digits then return tonumber(digits) end
  end
  return nil
end

-- Duplique le début de la REGION source après sa frontière pour la laisser
-- jouer une dernière fraction de cycle pendant le crossfade vers la région cible.
-- Les clones sont créés après le GO de la cible afin que l'exclusivité de piste
-- ne les supprime pas au moment du remplacement.
function X.clone_region_tail_for_crossfade(source_id, boundary, crossfade, cycle_start)
  crossfade = math.max(0, tonumber(crossfade) or 0)
  if not source_id or crossfade <= 0 or not boundary or not cycle_start then return end
  local snapshots = {}
  local end_at = cycle_start + crossfade

  for i = 0, reaper.CountMediaItems(PROJ) - 1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
    local _, keepalive = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_keepalive", "", false)
    local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
    local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
    local tk = reaper.GetActiveTake(it)
    if tostring(cid) == tostring(source_id) and keepalive ~= "1" and tk
      and pos >= cycle_start - 1e-5 and pos < end_at - 1e-5
      and not reaper.TakeIsMIDI(tk) then
      local src = reaper.GetMediaItemTake_Source(tk)
      local file = src and reaper.GetMediaSourceFileName(src, "")
      local rel = math.max(0, pos - cycle_start)
      local copy_len = math.min(len, crossfade - rel)
      if file and file ~= "" and copy_len > 0.001 then
        snapshots[#snapshots + 1] = {
          track = reaper.GetMediaItem_Track(it),
          file = file,
          pos = boundary + rel,
          len = copy_len,
          -- D_STARTOFFS est déjà l'offset source au début de l'item d'origine.
          -- Le clone démarre au même point de source, décalé dans la timeline.
          startoffs = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS"),
          rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE"),
          vol = reaper.GetMediaItemTakeInfo_Value(tk, "D_VOL"),
          pan = reaper.GetMediaItemTakeInfo_Value(tk, "D_PAN"),
          pitch = reaper.GetMediaItemTakeInfo_Value(tk, "D_PITCH"),
          chanmode = reaper.GetMediaItemTakeInfo_Value(tk, "I_CHANMODE"),
          itemvol = reaper.GetMediaItemInfo_Value(it, "D_VOL"),
          fadein = 0,
          source_id = tostring(source_id),
        }
      end
    end
  end

  for _, d in ipairs(snapshots) do
    local src = reaper.PCM_Source_CreateFromFile(d.file)
    if src then
      local it = reaper.AddMediaItemToTrack(d.track)
      local tk = reaper.AddTakeToMediaItem(it)
      if tk then
        reaper.SetMediaItemTake_Source(tk, src)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_STARTOFFS", d.startoffs)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_PLAYRATE", d.rate)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", d.vol)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_PAN", d.pan)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_PITCH", d.pitch)
        reaper.SetMediaItemTakeInfo_Value(tk, "I_CHANMODE", d.chanmode)
        reaper.SetMediaItemInfo_Value(it, "D_POSITION", d.pos)
        reaper.SetMediaItemInfo_Value(it, "D_LENGTH", d.len)
        reaper.SetMediaItemInfo_Value(it, "D_VOL", d.itemvol)
        reaper.SetMediaItemInfo_Value(it, "D_FADEINLEN", 0)
        reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", math.min(crossfade, d.len))
        -- Ne pas marquer cette copie comme une cue : replace_on_tracks la supprimerait
        -- en lançant B. Elle est temporaire et son fondu sortant termine le raccord.
        reaper.UpdateItemInProject(it)
      end
    end
  end
end

function X.fire_devamp_chain(next_id, crossfade, source_id, boundary, cycle_start)
  if not next_id then return false end
  local act = actions_by_id[next_id] or actions_by_id[tostring(next_id)]
  if act and X.is_playable_cue(act) then
    -- Le crossfade temporaire ne s'applique qu'à une destination REGION.
    -- Une destination AUDIO reste parfaitement valide, mais démarre sans crossfade de région.
    if X.is_region_cue(act) then
      act._devamp_fadein_override = math.max(0, tonumber(crossfade) or 0)
    else
      act._devamp_fadein_override = nil
    end
    -- Créer AVANT le GO de B une copie temporaire de la tête de boucle A.
    -- Elle n'a volontairement pas de P_EXT:cuelist_id : le remplacement exclusif
    -- de piste lors du GO de B ne la supprimera pas. Elle joue boundary -> boundary+xf.
    if X.is_region_cue(act) and tonumber(crossfade) and tonumber(crossfade) > 0 then
      X.clone_region_tail_for_crossfade(source_id, boundary, crossfade, cycle_start)
    end
    -- Le GO de B est placé à la frontière de A, et non au moment du pré-déclenchement.
    act._devamp_target_override = (X.is_region_cue(act) and tonumber(crossfade) and tonumber(crossfade) > 0)
      and tonumber(boundary) or nil
    X.fire_cue(act, true)
    act._devamp_fadein_override = nil
    act._devamp_target_override = nil
    return true
  end
  return false
end

function X.process_runs(now)
  if next(runs) == nil then return end
  if not X.is_playing() then
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
  local p = X.now_pos()
  for id, r in pairs(runs) do
    if not r.alive then
      X.remove_keepalive(id)
      runs[id] = nil
    else
      r.id = id
      local dest = X.find_track(r.dest_guid)
      if r.paused then
        -- Pause : ne plus étendre, conserver pause_src / pause_proj.
      elseif r.region_loop then
        -- Devamp région : déclencher B avant la fin de A pour permettre un vrai chevauchement.
        local boundary = r.next or 0
        local xf = math.min(math.max(0, tonumber(r.devamp_crossfade) or 0), math.max(0, tonumber(r.reg_len) or 0))
        local wants_devamp = r.devamp or r.devamp_armed or devamp_flags[id] or devamp_flags[tostring(id)]
        local next_act = r.devamp_next and (actions_by_id[r.devamp_next] or actions_by_id[tostring(r.devamp_next)])
        local next_is_region = next_act and X.is_region_cue(next_act)
        if wants_devamp and next_is_region and xf > 0 and r.devamp_next and not r.devamp_transition_started
          and p >= boundary - xf then
          r.devamp_transition_started = true
          -- Important : A ne doit PAS être arrêtée à la frontière. On conserve
          -- son cycle déjà planifié après boundary, puis on le fait sortir sur xf.
          local chain = r.devamp_next
          local cycle_start = boundary - (tonumber(r.reg_len) or 0)
          r.devamp_next = nil -- empêcher un second déclenchement à la frontière
          X.fire_devamp_chain(chain, xf, id, boundary, cycle_start)
        end
        -- À la fin du segment collé, re-déclencher ou sortir (Devamp / quota de cycles).
        if p >= boundary - 0.05 then
          local want_devamp = r.devamp or r.devamp_armed
            or devamp_flags[id] or devamp_flags[tostring(id)]
          local a = actions_by_id[id] or actions_by_id[tostring(id)]
          if not a then
            for _, tab in ipairs(tabs or {}) do
              for _, act in ipairs(tab.actions or {}) do
                if tostring(act.id) == tostring(id) then a = act; break end
              end
              if a then break end
            end
          end
          -- La case « Boucle » de l'action fait foi (jamais écrasée par le runtime).
          local loop_on = a and a.loop and a.loop ~= 0 and a.loop ~= "false"
          if loop_on and not want_devamp and a and X.is_region_cue(a) then
            r.loops_done = (r.loops_done or 0) + 1
            local lc = tonumber(a.loop_count)
            if lc and lc > 0 and r.loops_done >= lc then
              r.alive = false
              X.clear_devamp_state(id)
            else
              -- Re-GO : fire_cue recrée le run. Conserver le compteur de cycles
              -- déjà terminés, sinon il revient à zéro et un quota > 1 devient infini.
              local completed = r.loops_done or 0
              local limit = tonumber(a.loop_count)
              X.fire_cue(a, true)
              local nr = runs[a.id] or runs[tostring(a.id)]
              if nr and nr.region_loop then
                nr.loops_done = completed
                nr.loop_count = (limit and limit > 0) and limit or nil
              end
            end
          else
            local chain = want_devamp and r.devamp_next or nil
            r.alive = false
            X.clear_devamp_state(id)
            if chain then X.fire_devamp_chain(chain) end
          end
        end
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
              X.delete_cuelist_items({[tostring(id)] = true})
            end
            local chain = r.devamp_next
            runs[id] = nil
            devamp_flags[id] = nil
            devamp_flags[tostring(id)] = nil
            if chain then X.fire_devamp_chain(chain) end
          end
        else
          if want_devamp then
            -- DEVAMP : on laisse finir le passage Li→Lo (ou In→Lo) en cours,
            -- on supprime TOUS les passages déjà planifiés après lui, puis on
            -- enchaîne immédiatement Lo→OUT. Aucun saut de playhead.
            r.devamp, r.devamp_armed = true, true
            -- 1) Lister les items audio de la cue (position, fin, offset source).
            local list = {}
            X.cue_audio_items(dest, id, function(it, tk)
              local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
              local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
              local so  = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS")
              local rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE")
              list[#list+1] = {it = it, pos = pos, e = pos + len, so = so,
                               rate = (rate > 0 and rate or speed)}
            end)
            table.sort(list, function(a, b) return a.pos < b.pos end)
            -- 2) Choisir le dernier item conservé : le premier passage (In→Lo ou
            --    Li→Lo) qui finit assez loin devant la playhead. REAPER a déjà
            --    mis en tampon ce qui est imminent (latence audio) : un item
            --    Lo→OUT posé trop près de la tête serait joué en retard / décalé.
            local safe = p + math.max(margin / 1000, 0.15)
            local keep
            for _, x in ipairs(list) do
              if x.e > safe and x.pos < safe + cycle_proj + 1e-3
                 and math.abs((x.so + (x.e - x.pos) * x.rate) - lo) < 0.02 then
                keep = x; break
              end
            end
            if not keep then
              -- Repli : premier item qui finit après la zone de sécurité.
              for _, x in ipairs(list) do
                if x.e > safe then keep = x; break end
              end
            end
            local cut
            if keep then
              -- 3) Supprimer tout ce qui commence après l'item conservé.
              for _, x in ipairs(list) do
                if x.pos >= keep.e - 1e-4 and x.it ~= keep.it then
                  reaper.DeleteTrackMediaItem(dest, x.it)
                end
              end
              -- 4) Recaler la fin de l'item conservé EXACTEMENT sur Lo, pour que
              --    Lo→OUT se raccorde sans trou ni chevauchement.
              local exact = math.max(0.01, (lo - keep.so) / keep.rate)
              if keep.so < lo - 1e-4 then
                reaper.SetMediaItemInfo_Value(keep.it, "D_LENGTH", exact)
                reaper.SetMediaItemInfo_Value(keep.it, "D_FADEOUTLEN", 0)
                reaper.UpdateItemInProject(keep.it)
                cut = keep.pos + exact
              else
                cut = keep.e
              end
            else
              cut = math.max(r.next or 0, safe)
            end
            X.schedule_release(r, dest, cut)
          else
            local guard = 0
            while guard < 200 do
              -- Quota atteint : Lo→OUT est planifié tout de suite après le
              -- dernier passage (sinon REAPER s'arrête à la fin du dernier item).
              if r.loop_count and (r.loops_done or 0) >= r.loop_count then
                X.schedule_release(r, dest, r.next)
                break
              end
              if (r.next or 0) >= p + LOOP_HORIZON then break end
              local gain = (r.env and #r.env > 0) and X.env_gain(r.env, li) or 1
              X.add_file_item(dest, r.file, r.next, li, cycle, 0, gain, id, r.markers)
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
      
      -- STOP + fade sur boucle : rester en loop, baisser le volume, couper à la fin.
      if runs[id] and r.fade_out_end and not r.paused then
        local pnow = X.now_pos()
        local t0 = tonumber(r.fade_out_start) or pnow
        local t1 = tonumber(r.fade_out_end) or pnow
        local prog = (pnow - t0) / math.max(1e-6, t1 - t0)
        if prog >= 1 or pnow >= t1 then
          local sid = tostring(id)
          for ii = reaper.CountMediaItems(PROJ) - 1, 0, -1 do
            local it = reaper.GetMediaItem(PROJ, ii)
            local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
            if cid == sid then
              reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
            end
          end
          X.remove_keepalive(id)
          runs[id] = nil
          devamp_flags[id] = nil
          devamp_flags[tostring(id)] = nil
        else
          local g = 1 - math.max(0, math.min(1, prog))
          g = g * g
          local destf = X.find_track(r.dest_guid)
          if destf then
            local cue = actions_by_id[id] or actions_by_id[tostring(id)]
            local db = cue and tonumber(cue.wave_gain_db) or 0
            X.cue_audio_items(destf, id, function(it, tk)
              local envg = 1
              if r.env and #r.env > 0 then
                local so = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS") or r.tin
                envg = X.env_gain(r.env, so)
              end
              reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", envg * g * (10 ^ (db / 20)))
              reaper.UpdateItemInProject(it)
            end)
          end
        end
      end

      -- Suivi dynamique de l'enveloppe sur les items actifs
      if runs[id] and r.env and #r.env > 0 and dest and not r.paused and not r.fade_out_end then
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
                local v = X.cue_vol(id, r.env, rel_t)
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
function X.adjust_channels(tr, n)
  if not tr or not n or n < 1 then return nil end
  local need = n + (n % 2)
  local cur = math.floor(reaper.GetMediaTrackInfo_Value(tr, "I_NCHAN"))
  if need > cur then
    reaper.SetMediaTrackInfo_Value(tr, "I_NCHAN", need)
    return need
  end
  return nil
end

function X.create_track(name)
  local idx = reaper.CountTracks(PROJ)
  if reaper.InsertTrackInProject then
    reaper.InsertTrackInProject(PROJ, idx, 0)
  else
    X.on_main(function() reaper.InsertTrackAtIndex(idx, true) end)
  end
  local tr = reaper.GetTrack(PROJ, idx)
  if tr then reaper.GetSetMediaTrackInfo_String(tr, "P_NAME", name, true) end
  return tr
end

function X.replace_on_tracks(tracks, id, target, fade)
  -- fade <= 0 : mute + suppression immédiate des autres cues sur la piste.
  local sid = tostring(id)
  fade = tonumber(fade) or 0
  local hard = fade <= 0
  local p = X.now_pos()
  local t_cut = hard and p or target
  local t_end = t_cut + math.max(ANTICLICK, fade)
  local stopped = {}
  local track_set = {}
  for guid, tr in pairs(tracks) do
    track_set[guid] = tr
    if tr then track_set[reaper.GetTrackGUID(tr)] = tr end
  end

  -- Tuer les runs dont la destination est l'une de ces pistes.
  for rid, r in pairs(runs) do
    if r.alive and tostring(rid) ~= sid then
      local match = r.dest_guid and track_set[r.dest_guid]
      if match then
        r.alive = false
        stopped[#stopped + 1] = rid
      end
    end
  end

  for _, tr in pairs(track_set) do
    if tr then
      for i = reaper.CountTrackMediaItems(tr) - 1, 0, -1 do
        local it = reaper.GetTrackMediaItem(tr, i)
        local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
        if mark ~= "" and tostring(mark) ~= sid then
          local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
          local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
          if pos + len > t_cut then
            local tk = reaper.GetActiveTake(it)
            if hard then
              if tk and not reaper.TakeIsMIDI(tk) then
                reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", 0)
              end
              reaper.SetMediaItemInfo_Value(it, "D_VOL", 0)
              reaper.DeleteTrackMediaItem(tr, it)
            elseif pos >= t_cut then
              reaper.DeleteTrackMediaItem(tr, it)
            else
              local new_end = math.min(pos + len, t_end)
              reaper.SetMediaItemInfo_Value(it, "D_LENGTH", math.max(0.001, new_end - pos))
              reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", math.max(0, new_end - t_cut))
              reaper.UpdateItemInProject(it)
            end
            stopped[#stopped + 1] = tonumber(mark) or mark
          end
        end
      end
    end
  end
  if #stopped > 0 then X.kill_runs(stopped) end
end

---------------------------------------------------------------- Régions onglet
function X.stop_in(lib)
  X.with_proj(lib, function() reaper.OnStopButton() end)
end

function X.stop_ext(ids, dur)
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

function X.process_ext(now)
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
          X.stop_in(r.proj)
          reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0)
          ext_runs[id] = nil
        else
          reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0 * (1-p)^2)
        end
      elseif reaper.GetPlayPositionEx(r.proj) >= (r.reg_end or 0) - 1e-4 then
        local want_devamp = r.devamp or r.devamp_armed
          or devamp_flags[id] or devamp_flags[tostring(id)]
        -- Décision de reboucler : case de l'action si dispo, sinon flag du run.
        local act = actions_by_id[id] or actions_by_id[tostring(id)]
        local loop_on = r.loop
        if act then
          loop_on = act.loop and act.loop ~= 0 and act.loop ~= "false"
        end
        local can_loop = loop_on and not want_devamp
        if can_loop then
          local lc = tonumber(act and act.loop_count or r.loop_count)
          if lc and lc > 0 and (r.loops_done or 0) >= lc then can_loop = false end
        end
        if can_loop then
          r.loops_done = (r.loops_done or 0) + 1
          r.loop = true
          r.devamp = false
          r.devamp_armed = false
          r.devamp_next = nil
          X.with_proj(r.proj, function()
            reaper.SetEditCurPos2(r.proj, r.reg_start or 0, false, true)
          end)
        else
          local saved_next = (want_devamp and r.devamp_next) or nil
          X.clear_devamp_state(id)
          X.stop_in(r.proj)
          reaper.SetMediaTrackInfo_Value(r.master, "D_VOL", r.v0)
          ext_runs[id] = nil
          if saved_next then X.fire_devamp_chain(saved_next) end
        end
      elseif r.fadein and r.fadein > 0 and not r.fade_done then
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

function X.fire_cue_inplace(a, lib, reg)
  local master = reaper.GetMasterTrack(lib)
  local old = ext_runs[a.id]
  local v0 = old and old.v0 or reaper.GetMediaTrackInfo_Value(master, "D_VOL")
  local fadein = a.fadein or 0
  X.with_proj(lib, function()
    if (math.floor(reaper.GetPlayStateEx(lib)) & 1) ~= 0 then reaper.OnStopButton() end
    reaper.SetEditCurPos2(lib, reg.s, false, false)
    if fadein > 0 then reaper.SetMediaTrackInfo_Value(master, "D_VOL", 0) end
    reaper.OnPlayButton()
  end)
  local lc = tonumber(a.loop_count)
  if lc and lc <= 0 then lc = nil end
  local loop_on = (a.loop and a.loop ~= 0 and a.loop ~= "false") and true or false
  X.clear_devamp_state(a.id)
  ext_runs[a.id] = nil
  ext_runs[tostring(a.id)] = nil
  ext_runs[a.id] = {
    proj = lib, master = master,
    reg_start = reg.s, reg_end = reg.e, v0 = v0,
    t0 = reaper.time_precise(), fadein = fadein,
    loop = loop_on,
    loop_count = lc,
    loops_done = 0,
    devamp = false,
    devamp_armed = false,
    devamp_next = nil,
    id = a.id,
  }
  local pre = ""
  if a.has_snapshot and a.snap then
    local ntr = X.apply_snap(a, a.link_time and fadein or 0, 0)
    pre = string.format(" + snapshot (%d piste(s))", ntr)
  end
  local loop_txt = a.loop and " [loop]" or ""
  status = string.format("REGION \"%s\" : région \"%s\" jouée dans son onglet%s%s", a.name, reg.name, loop_txt, pre)
end

---------------------------------------------------------------- CUE
function X.release_holds()
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

function X.stop_previous(id, t_start, fade)
  -- Coupe les items de CET id. Retourne toujours t_start (placement de la nouvelle cue).
  -- Ne jamais renvoyer X.now_pos() : poser sous la playhead fait démarrer le fichier en cours.
  fade = tonumber(fade) or 0.03
  local hard = fade <= ANTICLICK + 1e-6
  local p = X.now_pos()
  local t_cut = hard and p or t_start
  local t_end = t_cut + math.max(ANTICLICK, fade)
  local sid = tostring(id)
  for i = reaper.CountMediaItems(PROJ) - 1, 0, -1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
    if tostring(mark) == sid then
      local _, ka = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_keepalive", "", false)
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      local tk = reaper.GetActiveTake(it)
      if ka == "1" or hard or pos >= t_cut then
        if tk and not reaper.TakeIsMIDI(tk) then
          reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", 0)
        end
        reaper.SetMediaItemInfo_Value(it, "D_VOL", 0)
        reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
      elseif pos + len > t_cut then
        local new_end = math.min(pos + len, t_end)
        reaper.SetMediaItemInfo_Value(it, "D_LENGTH", math.max(0.001, new_end - pos))
        reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", math.max(0, new_end - t_cut))
        reaper.UpdateItemInProject(it)
      end
    end
  end
  if runs[id] then runs[id].alive = false end
  if runs[sid] then runs[sid].alive = false end
  local n = tonumber(id)
  if n and runs[n] then runs[n].alive = false end
  return t_start
end

function X.fire_cue(a, from_chain)
  X.release_holds()
  -- Nouveau GO : oublier un Devamp collé, sans détruire le run tant que le fire n'a pas réussi.
  if a and a.id ~= nil then
    X.clear_devamp_state(a.id)
  end
  -- La boucle est gérée par la cue (Li/Lo) : on coupe le Repeat de REAPER pour
  -- éviter qu'il ne reboucle la lecture (conflit avec Devamp / suite jusqu'à OUT).
  if reaper.GetSetRepeat then reaper.GetSetRepeat(0) end
  local from_file = X.is_file_cue(a)
  if X.is_region_cue(a) then
    from_file = false
    a.src = "region"
  elseif from_file then
    a.src = "file"
  end
  local lib, reg

  if from_file then
    if not a.file or a.file == "" then
      status = "Cue \""..a.name.."\" : aucun fichier choisi."
      return
    end
    if not a.track or not X.find_track(a.track) then
      a.track = X.default_track_guid()
      if not a.track then
        status = "Cue \""..a.name.."\" : le projet ne contient aucune piste. Ajoute une piste puis réessaie."
        return
      end
      X.save()
    end
  else
    lib = X.find_project(a.projfn)
    if not lib then
      status = "Cue \""..a.name.."\" : projet source non ouvert."
      return
    end
    for _, r in ipairs(X.get_regions(lib)) do
      if r.idx == a.region then reg = r end
    end
    if not reg then
      status = "Cue \""..a.name.."\" : région introuvable."
      return
    end
    if lib ~= PROJ and not a.copy then
      X.fire_cue_inplace(a, lib, reg)
      return
    end
  end

  local dest = a.track and X.find_track(a.track)
  if a.track and not dest then
    status = "Cue \""..a.name.."\" : piste introuvable."
    return
  end

  local playing = X.is_playing()
  local fadein = tonumber(a._devamp_fadein_override) or tonumber(a.fadein) or 0
  -- Toujours placer DEVANT la playhead (sinon REAPER démarre le fichier en cours).
  -- Enchaînement FOLLOW/AUTO : look minimal pour éviter un trou audible.
  local exclusive_look
  if from_chain then
    exclusive_look = (fadein > 0) and math.max(0.02, math.min(0.08, fadein * 0.25)) or 0.01
  else
    exclusive_look = (fadein > 0) and math.max(margin / 1000, 0.05) or 0.04
  end
  local target = tonumber(a._devamp_target_override) or (X.now_pos() + exclusive_look)
  X.stop_previous(tostring(a.id), target, fadein > 0 and fadein or ANTICLICK)
  runs[a.id] = nil
  local count, missing, found = 0, nil, 0
  local used, notes = {}, {}

  local function mark(new)
    reaper.GetSetMediaItemInfo_String(new, "P_EXT:cuelist", "1", true)
    reaper.GetSetMediaItemInfo_String(new, "P_EXT:cuelist_id", tostring(a.id), true)
  end
  local function use_track(tr, nch)
    used[reaper.GetTrackGUID(tr)] = tr
    local n = X.adjust_channels(tr, nch)
    if n then notes[#notes+1] = X.track_name(tr).." portée à "..n.." canaux" end
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
      -- Couper les autres cues de cette piste AVANT de poser le nouvel item.
      if prefs.exclusive_track ~= false then
        X.replace_on_tracks(used, a.id, target, fadein)
      end
      local speed = X.cue_effective_speed(a, target)
      -- Recaler si la playhead a avancé pendant la préparation (toujours devant).
      do
        local now_t = X.now_pos() + exclusive_look
        if now_t > target then
          target = now_t
          X.stop_previous(tostring(a.id), target, fadein > 0 and fadein or ANTICLICK)
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
      local it = X.add_file_item(dest, a.file, target, first_src, first_seg, math.min(fadein, proj_seg), X.env_gain(env, first_src), a.id, a.markers)
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
            local tname = X.track_name(src_tr)
            d = X.find_track_by_name(tname)
            if not d then
              d = X.create_track(tname)
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
                X.copy_take_markers(tk, ntk)
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
            X.copy_take_markers(tk, ntk)
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
    X.replace_on_tracks(used, a.id, target, fadein)
  end
  reaper.PreventUIRefresh(-1)
  reaper.UpdateArrange()

  if count == 0 then
    status = missing and ("Cue \""..a.name.."\" : impossible de créer la piste \""..missing.."\".")
                     or (from_file and ("Cue \""..a.name.."\" : fichier illisible.")
                       or string.format("Cue \"%s\" : aucun item exploitable.", a.name))
    return
  end
  if not playing then
    X.play_main()
  elseif prefs.exclusive_track ~= false then
    -- Timeline déjà correcte : forcer le moteur audio à la relire.
    X.resync_play_engine()
  end
  cue_session = true

  -- Boucle région (mode copie) : un run surveille la fin du segment collé.
  if not from_file and a.loop and a.loop ~= 0 and a.loop ~= "false" and reg then
    local reg_len = math.max(0.05, (reg.e or 0) - (reg.s or 0))
    local lc = tonumber(a.loop_count)
    if lc and lc <= 0 then lc = nil end
    X.clear_devamp_state(a.id)
    runs[a.id] = nil
    runs[tostring(a.id)] = nil
    runs[a.id] = {
      region_loop = true,
      loop = true,
      alive = true,
      t0 = target,
      next = target + reg_len,
      reg_len = reg_len,
      id = a.id,
      loops_done = 0,
      loop_count = lc,
      dest_guid = a.track,
      paused = false,
      devamp = false,
      devamp_armed = false,
      devamp_next = nil,
    }

    -- Garde-fou silencieux : une boucle de région ne planifie qu'un seul
    -- passage à la fois. Après un Devamp, si aucun autre item ne prolonge le
    -- projet, REAPER peut arrêter le transport à la fin de ce passage avant
    -- que process_runs ait l'occasion de relancer la région. Un item MIDI vide
    -- maintient le transport en lecture ; il est supprimé avec les autres
    -- éléments de la cue au prochain GO / à la fin du run.
    local keep_track = X.keepalive_track()
    if keep_track and reaper.CreateNewMIDIItemInProj then
      local ka_start = target + reg_len
      local ka = reaper.CreateNewMIDIItemInProj(keep_track, ka_start, ka_start + 3600, false)
      if ka then
        reaper.GetSetMediaItemInfo_String(ka, "P_EXT:cuelist", "1", true)
        reaper.GetSetMediaItemInfo_String(ka, "P_EXT:cuelist_id", tostring(a.id), true)
        reaper.GetSetMediaItemInfo_String(ka, "P_EXT:cuelist_keepalive", "1", true)
      end
    end
  end

  local pre = ""
  if a.has_snapshot and a.snap then
    local ntr = X.apply_snap(a, a.link_time and fadein or 0, math.max(0, target - X.now_pos()))
    pre = string.format(" + snapshot (%d piste(s))", ntr)
  end
  local kind = from_file and "AUDIO" or "REGION"
  local loop_txt = (not from_file and a.loop) and " [loop]" or ""
  status = string.format("%s \"%s\" : %d item(s) à %.2f s%s%s%s",
    kind, a.name, count, target, loop_txt, pre,
    #notes > 0 and (" | "..table.concat(notes, ", ")) or "")
end

---------------------------------------------------------------- STOP
function X.cleanup_track(tr, keep)
  -- keep = true  → Delete on stop décoché : ne pas toucher aux items
  --                (ils restent entiers sur la timeline).
  -- keep = false → Delete on stop coché : tout supprimer sur la piste.
  if keep then return end
  for _, t in ipairs(X.tracks_of(tr)) do
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
X.delete_cuelist_items = function(cue_ids)
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

X.delete_all_cuelist_items = function()
  return X.delete_cuelist_items(nil)
end

-- Applique un fade-out natif sur la durée restante de l'item (sans le prolonger ni le boucler).
-- Si l'item est plus court que le fade demandé : tant pis, on fond sur ce qui reste.
-- On n'interrompt JAMAIS un item dont le fade est déjà en cours.
function X.apply_item_fadeout(it, t_start, t_end, fshape, allow_loop)
  local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
  local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
  local finish = pos + len
  if finish <= t_start then return false end
  if pos >= t_start then
    return "future" -- pas encore démarré
  end
  -- Ne pas raccourcir un item qui a déjà un fade-out en cours plus long.
  local existing_fo = reaper.GetMediaItemInfo_Value(it, "D_FADEOUTLEN") or 0
  if existing_fo > 0.02 then
    local fade_start = finish - existing_fo
    if t_start >= fade_start - 1e-4 then
      -- Déjà en train de fader : ne pas toucher.
      return true
    end
  end
  -- Couper au plus tôt à t_end, sans jamais dépasser la fin actuelle de l'item.
  local new_end = math.min(finish, t_end)
  if new_end <= pos + 0.005 then new_end = pos + 0.005 end
  local fo = math.max(0.005, new_end - t_start)
  -- fo ne peut pas dépasser la longueur restante de l'item après t_start
  fo = math.min(fo, new_end - pos)
  reaper.SetMediaItemInfo_Value(it, "D_LENGTH", math.max(0.005, new_end - pos))
  reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", fo)
  if fshape ~= nil then
    reaper.SetMediaItemInfo_Value(it, "D_FADEOUTSHAPE", fshape)
  end
  reaper.UpdateItemInProject(it)
  return true
end

function X.arm_fade_hold(dur)
  local hold = reaper.time_precise() + math.max(0.05, tonumber(dur) or 0) + 0.15
  if hold > fade_hold_until then fade_hold_until = hold end
end

function X.stop_all(dur)
  dur = dur or stop_fade
  X.stop_ext(nil, dur)
  local p = X.now_pos()
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

  -- 2) Items encore en cours / futurs.
  -- À durée 0, on ne planifie aucun fondu logiciel : on termine les items
  -- au curseur avec seulement 3 ms de fade anti-clic.
  if dur <= 0 then
    X.kill_runs(nil)
    local cutoff = p + ANTICLICK
    for i = reaper.CountMediaItems(PROJ)-1, 0, -1 do
      local it = reaper.GetMediaItem(PROJ, i)
      local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
      if mark == "1" then
        local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
        local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
        local finish = pos + len
        if finish > p then
          if pos >= cutoff then
            if prefs.delete_on_stop == true then
              reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
            else
              reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", ANTICLICK)
            end
          else
            local new_end = math.min(finish, cutoff)
            reaper.SetMediaItemInfo_Value(it, "D_LENGTH", math.max(0.001, new_end - pos))
            reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", math.min(ANTICLICK, math.max(0, new_end - pos)))
            if prefs.delete_on_stop == true then
              local _, guid = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
              del_jobs[#del_jobs + 1] = { at = reaper.time_precise() + ANTICLICK + 0.02, guids = {[guid]=true} }
            end
          end
        end
      end
    end
    reaper.UpdateArrange()
    X.resync_play_engine()
    status = "STOP : immédiat (protection anti-clic 3 ms)."
    return
  end

  -- FONDU NATIF : chaque item en cours est coupé à t_end et reçoit un vrai fade-out
  -- REAPER (D_FADEOUTLEN) qui commence à t_start. C'est évalué par le moteur audio,
  -- sans dépendre du script ni du retard de tampon (l'ancien fondu par D_VOL
  -- pouvait passer inaperçu). t_start = playhead + marge de latence.
  local t_start = p + math.max(margin / 1000, 0.05)
  local t_end = t_start + math.max(0.01, dur)
  -- Forme du fade-out REAPER selon le curseur "Courbe du STOP global" :
  -- jusqu'à 0.7 = la plus logarithmique possible (forme 3, chute immédiate) ;
  -- 0.7–0.8 rapide (1), 0.8–0.9 linéaire (0), 0.9–0.95 lent au début (2), au-delà (4).
  local fshape
  if stop_curve < 0.7 then fshape = 3
  elseif stop_curve < 0.8 then fshape = 1
  elseif stop_curve < 0.9 then fshape = 0
  elseif stop_curve < 0.95 then fshape = 2
  else fshape = 4 end
  local keep_mode = prefs.delete_on_stop ~= true
  X.arm_fade_hold(dur)
  X.begin_run_fades(nil, t_start, t_end)
  for i = reaper.CountMediaItems(PROJ)-1, 0, -1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist", "", false)
    if mark == "1" then
      local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
      if X.is_loop_fading_id(cid) then
        n = n + 1
      else
        local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
        local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
        local finish = pos + len
        if finish > t_start then
          n = n + 1
          local res = X.apply_item_fadeout(it, t_start, t_end, fshape, false)
          if res == "future" then
            if keep_mode then
              reaper.SetMediaItemInfo_Value(it, "B_MUTE", 1)
            else
              reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
            end
          end
        end
      end
    end
  end

  -- 3) Filet de sécurité : après le fondu, tout item ActionList restant disparaît.
  if prefs.delete_on_stop == true then
    del_jobs[#del_jobs + 1] = {
      at = reaper.time_precise() + math.max(0.01, dur) + math.max(margin / 1000, 0.05) + 0.15,
      all_cuelist = true
    }
  end
  if n > 0 then
    status = string.format("STOP : fondu natif %.1f s (%d item(s))%s",
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

function X.stop_targets(ids, dur)
  X.stop_ext(ids, dur)
  local set = {}
  for _, id in ipairs(ids) do set[tostring(id)] = true end
  local immediate = dur <= 0
  local t_start = X.now_pos() + (immediate and 0 or margin/1000)
  local effective_dur = immediate and ANTICLICK or dur
  local t_end = t_start + effective_dur
  local n, affected = 0, {}
  if immediate then
    X.kill_runs(ids)
  else
    X.arm_fade_hold(dur)
    X.begin_run_fades(ids, t_start, t_end)
  end
  for i = reaper.CountMediaItems(PROJ)-1, 0, -1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, mark = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
    if set[mark] then
      if (not immediate) and X.is_loop_fading_id(mark) then
        n = n + 1
      else
      local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
      local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
      if pos + len > t_start then
        n = n + 1
        if immediate then
          if pos >= t_start + ANTICLICK then
            if prefs.delete_on_stop == true then
              reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
            else
              reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", ANTICLICK)
            end
          else
            local new_end = math.min(pos + len, t_start + ANTICLICK)
            reaper.SetMediaItemInfo_Value(it, "D_LENGTH", math.max(0.001, new_end - pos))
            reaper.SetMediaItemInfo_Value(it, "D_FADEOUTLEN", math.min(ANTICLICK, math.max(0, new_end-pos)))
            if prefs.delete_on_stop == true then
              local _, g = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
              affected[g] = true
            end
          end
        else
          -- Fondu long : prolonger l'item si besoin pour tenir toute la durée.
          local res = X.apply_item_fadeout(it, t_start, t_end, nil, true)
          if res == "future" then
            if prefs.delete_on_stop == true then
              reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
            else
              reaper.SetMediaItemInfo_Value(it, "B_MUTE", 1)
            end
          elseif res and prefs.delete_on_stop == true then
            local _, g = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
            affected[g] = true
          end
        end
      end
      end -- not loop-fading
    end
  end
  if prefs.delete_on_stop == true then
    local id_set = {}
    for id in pairs(set) do id_set[id] = true end
    del_jobs[#del_jobs + 1] = {
      at = reaper.time_precise() + (immediate and ANTICLICK or margin/1000 + dur) + 0.05,
      cue_ids = id_set,
      guids = next(affected) and affected or nil
    }
  end
  reaper.UpdateArrange()
  -- Comme pour le STOP global, forcer REAPER à reconstruire la lecture à partir
  -- des items modifiés : sinon le moteur peut continuer à lire son audio préchargé
  -- pendant près d'une seconde avant d'appliquer le STOP ciblé.
  X.resync_play_engine()
  status = immediate
    and string.format("STOP ciblé immédiat (protection 3 ms) : %d item(s)%s", n, prefs.delete_on_stop == true and " → suppression" or " (items conservés)")
    or string.format("STOP ciblé : fade de %.1f s, %d item(s)%s", dur, n, prefs.delete_on_stop == true and " → suppression" or " (items conservés)")
end

function X.apply_linked_snapshot(a, dur)
  if a.has_snapshot and a.snap then
    local ntr = X.apply_snap(a, a.link_time and (dur or 0) or 0, 0)
    status = (status or "") .. string.format(" + snapshot (%d piste(s))", ntr)
  end
end

function X.fire_stop(a)
  local dur = math.max(0, tonumber(a.dur) or 0) -- 0 = arrêt immédiat ; la protection de 3 ms est appliquée aux items
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
    stop_until[a.id] = reaper.time_precise() + math.max(0.003, dur) + 0.2
  end
  if targeted then X.stop_targets(a.targets, dur) else X.stop_all(dur) end
  X.apply_linked_snapshot(a, dur)
  -- Arrêt du transport = option "Arrêter la lecture…", UNIQUEMENT après la fin du fade.
  if prefs.auto_stop == true then
    local wait = (dur > 0) and (dur + math.max(margin / 1000, 0.05) + 0.1) or 0.01
    X.arm_fade_hold(dur)
    del_jobs[#del_jobs + 1] = {
      at = reaper.time_precise() + wait,
      stop_transport = true
    }
  end
end

function X.target_run_ids(a)
  local ids = X.resolve_targets(a)
  if ids then return ids end
  local all = {}
  for id in pairs(runs) do all[#all+1] = id end
  return all
end

function X.fire_pause(a)
  local fade = math.max(0, tonumber(a.dur) or 0)
  local n = 0
  local skipped_regions = 0
  for _, id in ipairs(X.target_run_ids(a)) do
    local source_cue = actions_by_id[id] or actions_by_id[tostring(id)]
    -- Pause/unpause d'une région n'est pas pris en charge : ne jamais appeler
    -- le moteur de pause sur ce type, y compris depuis une ancienne ActionList.
    if source_cue and X.is_region_cue(source_cue) then
      skipped_regions = skipped_regions + 1
    elseif a.unpause == true then
      if X.resume_run(id, fade) then n = n + 1 end
    else
      if X.pause_run(id, fade) then n = n + 1 end
    end
  end
  status = string.format("%s : %d cue(s) concernée(s)%s%s.", a.unpause == true and "UNPAUSE" or "PAUSE", n,
    fade > 0 and string.format(", fade %.1f s", fade) or "",
    skipped_regions > 0 and string.format(" — %d cible(s) REGION ignorée(s) (non prises en charge)", skipped_regions) or "")
  if a.id then stop_until[a.id] = nil end
  X.apply_linked_snapshot(a, fade)
end

function X.fire_devamp(a)
  local next_id = X.resolve_devamp_next(a)
  local n, any_chain = 0, false
  for _, id in ipairs(X.target_run_ids(a)) do
    local source_cue = actions_by_id[id] or actions_by_id[tostring(id)]
    local run_next, run_crossfade = next_id, a.devamp_crossfade
    -- Une source AUDIO sort toujours sur sa propre boucle/OUT : elle ne reçoit
    -- jamais de destination post-Devamp, même si un ancien réglage est sauvegardé.
    if source_cue and X.is_file_cue(source_cue) then
      run_next, run_crossfade = nil, 0
    end
    if X.devamp_run(id, run_next, run_crossfade) then
      n = n + 1
      if run_next then any_chain = true end
    end
  end
  local nxt = any_chain and next_id and (" → Q"..tostring(next_id)) or ""
  status = string.format("DEVAMP : %d cue(s) armée(s)%s.", n, nxt)
  X.apply_linked_snapshot(a, 0)
end

---------------------------------------------------------------- Nettoyage
---------------------------------------------------------------- SNAPSHOT
function X.capture(tr)
  local p = {
    vol = reaper.GetMediaTrackInfo_Value(tr, "D_VOL"),
    pan = reaper.GetMediaTrackInfo_Value(tr, "D_PAN"),
    mute = reaper.GetMediaTrackInfo_Value(tr, "B_MUTE") >= 0.5,
    solo = math.floor(reaper.GetMediaTrackInfo_Value(tr, "I_SOLO") + 0.5), -- 0 / 1 / 2 (SIP)
    arm  = reaper.GetMediaTrackInfo_Value(tr, "I_RECARM") >= 0.5,
    fx = {},
    sends = {}
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
  -- Sends piste (cat 0) + sorties hardware (cat 2)
  for _, cat in ipairs({0, 2}) do
    for i = 0, reaper.GetTrackNumSends(tr, cat) - 1 do
      local dest_guid = nil
      if cat == 0 then
        local dest = reaper.GetTrackSendInfo_Value(tr, cat, i, "P_DESTTRACK")
        -- Ne PAS utiliser ValidatePtr2(PROJ, …) : la piste peut appartenir
        -- au projet cible du preset (a.snap_projfn / a.projfn), pas au projet courant.
        if dest then
          dest_guid = reaper.GetTrackGUID(dest)
        end
      end
      p.sends[#p.sends+1] = {
        cat = cat,
        idx = i,
        dest = dest_guid,
        vol = reaper.GetTrackSendInfo_Value(tr, cat, i, "D_VOL"),
        pan = reaper.GetTrackSendInfo_Value(tr, cat, i, "D_PAN"),
        mute = reaper.GetTrackSendInfo_Value(tr, cat, i, "B_MUTE") >= 0.5,
      }
    end
  end
  return p
end

-- Retrouve l'index d'un send (par destination GUID si possible).
-- Ne PAS utiliser ValidatePtr2(PROJ, …) : la piste peut appartenir à un autre
-- projet que PROJ (preset ciblant un autre onglet). La comparaison de GUID suffit.
function X.resolve_send_idx(tr, cat, dest_guid, fallback_idx)
  if cat == 0 and dest_guid then
    for i = 0, reaper.GetTrackNumSends(tr, 0) - 1 do
      local dest = reaper.GetTrackSendInfo_Value(tr, 0, i, "P_DESTTRACK")
      if dest and reaper.GetTrackGUID(dest) == dest_guid then
        return i
      end
    end
  end
  local n = reaper.GetTrackNumSends(tr, cat)
  if fallback_idx and fallback_idx >= 0 and fallback_idx < n then return fallback_idx end
  return nil
end

function X.apply_steps(steps, p)
  for _, s in ipairs(steps) do
    if s.k == "vol" then
      reaper.SetMediaTrackInfo_Value(s.tr, "D_VOL", X.lerp_db(s.from, s.to, p))
    elseif s.k == "pan" then
      reaper.SetMediaTrackInfo_Value(s.tr, "D_PAN", s.from + (s.to - s.from)*p)
    elseif s.k == "sendvol" then
      local idx = X.resolve_send_idx(s.tr, s.cat, s.dest, s.idx)
      if idx then
        reaper.SetTrackSendInfo_Value(s.tr, s.cat, idx, "D_VOL", X.lerp_db(s.from, s.to, p))
      end
    elseif s.k == "sendpan" then
      local idx = X.resolve_send_idx(s.tr, s.cat, s.dest, s.idx)
      if idx then
        reaper.SetTrackSendInfo_Value(s.tr, s.cat, idx, "D_PAN", s.from + (s.to - s.from)*p)
      end
    else
      reaper.TrackFX_SetParamNormalized(s.tr, s.fx, s.p, s.from + (s.to - s.from)*p)
    end
  end
end

function X.ensure_snap(a)
  if not a.snap and a.data and a.track then
    a.snap = {order={a.track}, tracks={[a.track]=a.data}}
    a.data = nil
    X.save()
  end
end

function X.snap_add(snap, tr)
  local g = reaper.GetTrackGUID(tr)
  local st = X.capture(tr)
  st.name = X.track_name(tr)
  st.include = true
  snap.order[#snap.order+1] = g
  snap.tracks[g] = st
end

function X.current_value(s)
  if s.k == "vol" then return reaper.GetMediaTrackInfo_Value(s.tr, "D_VOL")
  elseif s.k == "pan" then return reaper.GetMediaTrackInfo_Value(s.tr, "D_PAN")
  elseif s.k == "sendvol" or s.k == "sendpan" then
    local idx = X.resolve_send_idx(s.tr, s.cat, s.dest, s.idx)
    if not idx then return s.to end
    local parm = (s.k == "sendvol") and "D_VOL" or "D_PAN"
    return reaper.GetTrackSendInfo_Value(s.tr, s.cat, idx, parm)
  else return reaper.TrackFX_GetParamNormalized(s.tr, s.fx, s.p) end
end

function X.start_morph(m)
  m.started = true
  local keys, kept = {}, {}
  for _, s in ipairs(m.steps) do
    s.from = X.current_value(s)
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
  for _, f in ipairs(m.track_flags or {}) do
    if f.k == "mute" then
      reaper.SetMediaTrackInfo_Value(f.tr, "B_MUTE", f.val)
    elseif f.k == "solo" then
      reaper.SetMediaTrackInfo_Value(f.tr, "I_SOLO", f.val)
    elseif f.k == "arm" then
      reaper.SetMediaTrackInfo_Value(f.tr, "I_RECARM", f.val)
    elseif f.k == "sendmute" then
      local idx = X.resolve_send_idx(f.tr, f.cat, f.dest, f.idx)
      if idx then
        reaper.SetTrackSendInfo_Value(f.tr, f.cat, idx, "B_MUTE", f.val)
      end
    end
  end
end

X.apply_snap = function(a, dur, delay)
  X.ensure_snap(a)
  local use = a.use or {vol=true, pan=true, mute=true, solo=true, arm=true, fxen=true, fxpar=true, send=true}
  if use.send == nil then use.send = true end
  local steps, enables, track_flags, warns, ntr = {}, {}, {}, {}, 0
  if not a.snap then return 0, warns end
  -- Projet cible du snapshot :
  --   - SNAPSHOT autonome → a.projfn
  --   - snapshot lié      → a.snap_projfn (a.projfn d'un CUE désigne sa région
  --                          source, on ne doit PAS le confondre avec le projet
  --                          du snapshot lié).
  local target_projfn
  if a.type == "snapshot" then
    target_projfn = a.projfn
  else
    target_projfn = a.snap_projfn
  end
  local lib = PROJ
  if target_projfn and target_projfn ~= "" then
    lib = X.find_project(target_projfn)
    if not lib then
      warns[#warns+1] = "projet source du snapshot introuvable (fermé ?)"
      return 0, warns
    end
  end
  for _, g in ipairs(a.snap.order) do
    local d = a.snap.tracks[g]
    local tr = X.find_track(g, lib)
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
        -- Mute / Solo / Arm : appliqués immédiatement au démarrage du morph (comme les enables FX).
        if use.mute and d.mute ~= nil then
          track_flags[#track_flags+1] = {tr=tr, k="mute", val=d.mute and 1 or 0}
        end
        if use.solo and d.solo ~= nil then
          track_flags[#track_flags+1] = {tr=tr, k="solo", val=tonumber(d.solo) or 0}
        end
        if use.arm and d.arm ~= nil then
          track_flags[#track_flags+1] = {tr=tr, k="arm", val=d.arm and 1 or 0}
        end
        if use.send and type(d.sends) == "table" then
          for si, sd in ipairs(d.sends) do
            local cat = tonumber(sd.cat) or 0
            local key_base = g.."|send|"..tostring(cat).."|"..(sd.dest or si)
            if sd.vol ~= nil then
              steps[#steps+1] = {
                k="sendvol", tr=tr, cat=cat, idx=sd.idx, dest=sd.dest,
                to=sd.vol, key=key_base.."|vol"
              }
            end
            if sd.pan ~= nil then
              steps[#steps+1] = {
                k="sendpan", tr=tr, cat=cat, idx=sd.idx, dest=sd.dest,
                to=sd.pan, key=key_base.."|pan"
              }
            end
            if sd.mute ~= nil then
              track_flags[#track_flags+1] = {
                tr=tr, k="sendmute", cat=cat, idx=sd.idx, dest=sd.dest,
                val=sd.mute and 1 or 0
              }
            end
          end
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
              warns[#warns+1] = X.track_name(tr).." : effet "..i.." différent"
            end
          end
        end
      end
    end
  end
  dur, delay = dur or 0, delay or 0
  local m = {
    steps = steps, enables = enables, track_flags = track_flags,
    t0 = reaper.time_precise() + math.max(0, delay),
    dur = math.max(dur, 0.001)
  }
  if dur <= 0 and delay <= 0 then
    X.start_morph(m)
    X.apply_steps(m.steps, 1)
  else
    morphs[#morphs+1] = m
  end
  return ntr, warns
end

function X.fire_snapshot(a)
  X.ensure_snap(a)
  if not a.snap or #a.snap.order == 0 then
    status = "SNAPSHOT \""..a.name.."\" : rien de capturé."
    return
  end
  local ntr, warns = X.apply_snap(a, a.dur or 0, 0)
  status = string.format("SNAPSHOT \"%s\" : %d piste(s)", a.name, ntr)
    .. (#warns > 0 and (" - "..table.concat(warns, ", ")) or "")
end

---------------------------------------------------------------- OSC / MIDI
X.led = {} -- id d'action -> instant du dernier envoi (témoin LED)
function X.send_osc(port_def, address, args)
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
    return true
  else
    status = "OSC : échec d'envoi ("..tostring(err)..")"
    return false
  end
end

function X.fire_osc(a)
  local port_def
  for _, p in ipairs(prefs.ports or {}) do
    if p.name == a.port_name then port_def = p break end
  end
  if not port_def then
    status = "OSC \""..(a.name or "").."\" : port \""..(a.port_name or "").."\" introuvable."
    return
  end
  if X.send_osc(port_def, a.address or "/", a.args) then X.led[a.id] = reaper.time_precise() end
end

-- Configure la piste relais : Virtual Keyboard + arm + monitoring.
function X.ensure_track_midi_vkb(tr)
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

function X.ensure_midi_relay_track()
  local tr = X.find_track_by_name(MIDI_RELAY_NAME)
  if not tr then
    tr = X.create_track(MIDI_RELAY_NAME)
  end
  if tr then X.ensure_track_midi_vkb(tr) end
  return tr
end

-- Rebuild des sends MIDI-only depuis la relais vers chaque destination connue.
function X.rebuild_midi_relay_sends(relay)
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

function X.ensure_midi_relay_to(dest)
  local relay = X.ensure_midi_relay_track()
  if not relay or not dest then return nil end
  local guid = reaper.GetTrackGUID(dest)
  if not midi_relay_dests[guid] then
    midi_relay_dests[guid] = dest
    X.rebuild_midi_relay_sends(relay)
  else
    midi_relay_dests[guid] = dest
    -- S'assurer que la relais est toujours armée même si le send existe déjà.
    X.ensure_track_midi_vkb(relay)
  end
  return relay
end

function X.fire_midi(a)
  local tr = a.track and X.find_track(a.track)
  if not tr then
    status = 'MIDI "'..(a.name or "")..'" : piste cible introuvable.'
    return
  end
  if type(reaper.StuffMIDIMessage) ~= "function" then
    status = "MIDI : StuffMIDIMessage indisponible dans cette version de REAPER."
    return
  end

  local relay = X.ensure_midi_relay_to(tr)
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

  X.led[a.id] = reaper.time_precise()
  status = string.format('MIDI "%s" → « %s » via relais « %s » (%s, canal %d)',
    a.name or "", X.track_name(tr), MIDI_RELAY_NAME, detail, ch + 1)
end

function X.poll_midi_note_offs()
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

function X.parse_q_ids(name)
  local ids = {}
  if not name then return ids end
  for token in name:gmatch("[Qq]%s*([%d%.]+)") do
    local n = tonumber(token)
    if n then ids[#ids+1] = n end
  end
  return ids
end

function X.clear_fired_for_project(project_key)
  local prefix = project_key .. "|"
  for key in pairs(fired_markers) do
    if key:sub(1, #prefix) == prefix then fired_markers[key] = nil end
  end
end

function X.action_for_qid(qid)
  return actions_by_id[qid] or actions_by_id[tostring(qid)] or actions_by_id[tonumber(qid)]
end

function X.fire_qids_once(project_key, guid, abspos, qids)
  for _, qid in ipairs(qids or {}) do
    local key = project_key .. "|" .. tostring(guid) .. "|Q|" .. tostring(qid) .. "|" .. string.format("%.4f", abspos)
    if not fired_markers[key] then
      local act = X.action_for_qid(qid)
      fired_markers[key] = true
      if act then
        X.fire(act)
      else
        status = string.format("Marqueur Q%s détecté, mais aucun cue avec l'ID %s n'existe dans cette ActionList.", tostring(qid), tostring(qid))
      end
    end
  end
end

function X.process_take_markers(now)
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
      X.clear_fired_for_project(project_key)
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
              local qids = X.parse_q_ids(mname)
              if #qids > 0 then
                local rel = (mpos - startoffs) / rate
                local abs = pos + rel
                local valid_in_item = rel >= -0.02 and rel <= len + 0.02
                if valid_in_item and abs >= lower_bound and abs <= p + look_ahead then
                  X.fire_qids_once(project_key, guid, abs, qids)
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
function X.process_jobs()
  local now = reaper.time_precise()
  if play_check and now >= play_check then
    play_check = nil
    if not X.is_playing() then
      status = "Attention : la lecture n'a pas démarré."
    end
  end
  X.process_runs(now)
  X.process_ext(now)
  X.refresh_active(now)
  X.process_take_markers(now)
  -- Arrêt transport = option "Arrêter la lecture quand plus aucun média…".
  -- Delete on stop = suppression des items uniquement (indépendant).
  -- Tant qu'un FOLLOW (ou AUTO) est actif, on ne doit NI arrêter le transport
  -- NI repositionner le curseur : sinon la tête de lecture n'atteint jamais
  -- follow_end et l'enchaînement reste bloqué.
  local chain_active = auto_chain ~= nil
  local fade_active = reaper.time_precise() < (fade_hold_until or 0)
  if prefs.auto_stop == true and not chain_active and not fade_active then
    if X.is_playing() then
      np_since = nil
      if cue_session and now - last_scan > 0.25 then
        last_scan = now
        local still_busy = (next(runs) ~= nil)
        if X.active_cue_items() or still_busy then
          idle_since = nil
        else
          idle_since = idle_since or now
          if now - idle_since >= 0.3 then
            if prefs.delete_on_stop == true then X.delete_all_cuelist_items() end
            X.stop_here() -- revient au point de départ de la session
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
  -- Protégé pendant un FOLLOW/AUTO pour ne pas faire sauter la playhead.
  if not X.is_playing() then
    np_since = np_since or now
  else
    np_since = nil
  end
  if prefs.delete_on_stop == true and cue_session and not X.is_playing() and not chain_active then
    if np_since and (now - np_since) > 0.5 then
      local n = X.delete_all_cuelist_items()
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
      local keep_job = false
      if j.stop_transport then
        if reaper.time_precise() < (fade_hold_until or 0) or auto_chain then
          j.at = math.max(j.at, (fade_hold_until or 0) + 0.05)
          keep_job = true
        elseif prefs.auto_stop == true then
          X.stop_here()
          cue_session = false
        end
      elseif prefs.delete_on_stop == true then
        -- Ne supprimer que si l'option est ENCORE active au moment de l'exécution.
        if j.all_cuelist then
          X.delete_all_cuelist_items()
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
      if not keep_job then
        table.remove(del_jobs, i)
      end
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
        -- Dernier pas : volume à 0 (sinon il reste le gain du dernier pas, non nul).
        for _, saved in ipairs(j.items or {}) do
          for k = 0, reaper.CountMediaItems(PROJ)-1 do
            local it = reaper.GetMediaItem(PROJ, k)
            local _, guid = reaper.GetSetMediaItemInfo_String(it, "GUID", "", false)
            if guid == saved.guid then
              reaper.SetMediaItemInfo_Value(it, "D_VOL", 0)
              break
            end
          end
        end
        X.cleanup_track(j.tr, j.keep)
        j.done = now
      else
        -- Courbe de gain du fade-out (amplitude = (1-p)^k) :
        -- minimum = logarithmique marqué (k=4 : le niveau baisse très vite),
        -- milieu  = k=2 (≈ perception régulière de l'oreille, au lieu d'un
        --           linéaire en amplitude qui paraît "inactif" au début),
        -- maximum = exponentiel (k=0.5 : le niveau reste haut puis chute à la fin).
        local k
        if stop_curve <= 0.5 then
          k = 4 - 4 * stop_curve          -- 4 -> 2
        else
          k = 2 - 3 * (stop_curve - 0.5)  -- 2 -> 0.5
        end
        local gain = (1 - p) ^ k
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
      if not m.started then X.start_morph(m) end
      local p = (now - m.t0) / m.dur
      X.apply_steps(m.steps, math.min(1, p))
      if p >= 1 or #m.steps == 0 then table.remove(morphs, i) end
    end
  end
end

---------------------------------------------------------------- Fire
X.fire = function(a, from_auto_chain)
  if not a then return end
  -- Toute action déclenchée manuellement remplace le compte à rebours précédent.
  if not from_auto_chain then auto_chain = nil end
  if X.is_playable_cue(a) then X.fire_cue(a, from_auto_chain)
  elseif a.type == "snapshot" then X.fire_snapshot(a)
  elseif a.type == "stop"   then X.fire_stop(a)
  elseif a.type == "pause"  then X.fire_pause(a)
  elseif a.type == "devamp" then X.fire_devamp(a)
  elseif a.type == "osc"    then X.fire_osc(a)
  elseif a.type == "midi"   then X.fire_midi(a)
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
        if X.is_playable_cue(a) then
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
          -- Snapshot / OSC / MIDI : action instantanée, puis DELAY.
          wait_until = now
        end
      end
      auto_chain = {
        source_id = a.id,
        next_id = actions[idx + 1].id,
        tab_index = active_tab,
        mode = a.follow == true and "follow" or "auto",
        wait_for_run = wait_for_run,
        follow_end = (a.follow == true and X.is_playable_cue(a) and runs[a.id] and not runs[a.id].loop)
          and ((tonumber(runs[a.id].t0) or X.now_pos()) + math.max(0, tonumber(runs[a.id].proj_seg or runs[a.id].seg) or 0)) or nil,
        delay_started = false,
        delay = delay,
        deadline = wait_until + delay,
      }
    end
  end
end

function X.process_auto_chain()
  local chain = auto_chain
  if not chain then return end
  -- Ne pas lancer une cue d'un onglet devenu inactif ni un ID qui a été supprimé.
  if chain.tab_index ~= active_tab then auto_chain = nil; return end
  local now = reaper.time_precise()
  -- FOLLOW sur une cue audio attend la fin réelle prévue de sa lecture.
  if chain.mode == "follow" then
    local run = runs[chain.source_id]
    -- Boucle : attendre l'arrêt réel du run (STOP / Devamp), jamais de relance.
    if chain.wait_for_run and run and run.loop then return end
    if chain.follow_end then
      local pos = X.now_pos()
      local playing = X.is_playing()
      if playing then chain.seen_play = true end
      local run_gone = (run == nil)
      -- Anticiper légèrement la fin (buffer audio) pour enchaîner sans trou.
      local ended = (pos >= chain.follow_end - 0.03)
        or (chain.seen_play and not playing and run_gone)
        or (chain.seen_play and not playing and pos >= chain.follow_end - 0.5)
      if ended then
        -- Libérer le run source tout de suite (évite d'attendre le +0.15 s de process_runs).
        if run then
          runs[chain.source_id] = nil
          runs[tostring(chain.source_id)] = nil
        end
        if not chain.delay_started then
          chain.delay_started = true
          local d = math.max(0, tonumber(chain.delay) or 0)
          chain.deadline = now + d
          if d <= 0 then
            -- Enchaînement immédiat : ne pas attendre la frame suivante.
            chain.deadline = now
          end
        end
      else
        chain.delay_started = false
        chain.deadline = math.huge
        return
      end
    elseif chain.wait_for_run then
      if run then return end
      chain.wait_for_run = false
      if not chain.delay_started then
        chain.delay_started = true
        chain.deadline = now + math.max(0, tonumber(chain.delay) or 0)
      end
    end
  end
  if now < chain.deadline then return end
  -- Enchaînement : uniquement la cue SUIVANTE, jamais la source.
  local next_id = chain.next_id
  local source_id = chain.source_id
  local chain_mode = chain.mode
  auto_chain = nil
  if next_id == nil or next_id == source_id then
    status = (chain_mode == "follow" and "FOLLOW" or "AUTO") .. " : pas de cue suivante."
    return
  end
  -- FOLLOW : la source est terminée → on la coupe pour éviter qu'elle continue / se relance.
  -- AUTO : on ne touche PAS à la source : elle peut continuer (pistes différentes).
  --        Si même piste, exclusive_track dans fire_cue gère le remplacement.
  if chain_mode == "follow" and source_id ~= nil then
    X.kill_runs({source_id})
    local sid = tostring(source_id)
    for i = reaper.CountMediaItems(PROJ) - 1, 0, -1 do
      local it = reaper.GetMediaItem(PROJ, i)
      local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
      if cid == sid then
        reaper.DeleteTrackMediaItem(reaper.GetMediaItem_Track(it), it)
      end
    end
    devamp_flags[source_id] = nil
    devamp_flags[tostring(source_id)] = nil
  end
  for i, candidate in ipairs(actions) do
    if candidate.id == next_id then
      -- N° rouge = première cue PAS encore déclenchée (= celle après celle qu'on enchaîne).
      -- Sinon un GO manuel relancerait la dernière cue auto-exécutée.
      if actions[i + 1] then
        selected = actions[i + 1].id
      else
        selected = candidate.id
      end
      X.fire(candidate, true)
      return
    end
  end
  status = (chain_mode == "follow" and "FOLLOW" or "AUTO")
    .. " : cue suivante introuvable (ID " .. tostring(next_id) .. ")."
end

---------------------------------------------------------------- Interface utilitaires
function X.mods_shift_multi()
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

function X.pick_only(a, i)
  picked = {[a.id] = true}
  pick_anchor = i
  selected = a.id
end

-- Supprime les actions sélectionnées par leur titre (liste active).
function X.delete_picked()
  local n, first_i = 0, nil
  for i = #actions, 1, -1 do
    if picked[actions[i].id] then
      if selected == actions[i].id then selected = nil end
      table.remove(actions, i)
      n = n + 1
      first_i = i
    end
  end
  if n == 0 then return false end
  picked = {}
  pick_anchor = nil
  if not selected and #actions > 0 then
    local nxt = actions[math.min(first_i or 1, #actions)]
    picked = {[nxt.id] = true}; selected = nxt.id; pick_anchor = math.min(first_i or 1, #actions)
  end
  X.save()
  status = n .. " action(s) supprimée(s) (Ctrl/Cmd+Suppr)."
  return true
end

function X.pick_range(from_i, to_i)
  if from_i > to_i then from_i, to_i = to_i, from_i end
  picked = {}
  for i = from_i, to_i do
    picked[actions[i].id] = true
  end
end


-- Presse-papiers interne pour copier/couper plusieurs cues sélectionnées,
-- même si elles proviennent de plusieurs onglets.
function X.collect_picked_actions()
  local out = {}
  for ti, tab in ipairs(tabs or {}) do
    for ai, a in ipairs(tab.actions or {}) do
      if picked[a.id] then
        out[#out+1] = {action = X.clone_table(a), tab_index = ti, action_index = ai, id = a.id}
      end
    end
  end
  return out
end

function X.copy_picked_actions(cut)
  local items = X.collect_picked_actions()
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
    X.sync_active_tab()
    picked, pick_anchor = {}, nil
    if selected and ids[selected] then selected = nil end
    X.save()
    status = tostring(#items) .. " cue(s) coupée(s). Colle avec Ctrl/Cmd+V."
  else
    status = tostring(#items) .. " cue(s) copiée(s). Colle avec Ctrl/Cmd+V."
  end
end

function X.paste_picked_actions()
  if type(cue_clipboard) ~= "table" or #cue_clipboard == 0 then
    status = "Le presse-papiers des cues est vide."
    return
  end
  local pasted_ids = {}
  for _, item in ipairs(cue_clipboard) do
    local a = X.normalize_action(X.clone_table(item.action or item))
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
  X.save()
  status = tostring((function() local n=0; for _ in pairs(pasted_ids) do n=n+1 end; return n end)()) .. " cue(s) collée(s) dans « " .. tostring(tabs[active_tab].name or "liste active") .. " »."
end

function X.move_rows(from, to)
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
  -- La liste affichée a été recréée : la rattacher à son onglet, sinon les cues créées
  -- ensuite n'existent que dans `actions` (introuvables par les captures, les marqueurs,
  -- la table des IDs, et perdues à la réouverture).
  if tabs[active_tab] then tabs[active_tab].actions = actions end
  X.save()
end

function X.go_selected()
  local si
  for i, a in ipairs(actions) do if a.id == selected then si = i end end
  if not si then status = "Aucune action sélectionnée." return end
  X.fire(actions[si])
  if actions[si+1] then
    X.pick_only(actions[si+1], si+1)
  end
end

X.TYPE_LABEL = {audio="AUDIO", region="REGION", snapshot="SNAPSHOT", stop="STOP", pause="PAUSE", devamp="DEVAMP", osc="OSC", midi="MIDI"}

-- Cues jouables : fichier audio (type audio) ou région (type region).
function X.is_playable_cue(a)
  return a and (a.type == "audio" or a.type == "region")
end
function X.is_file_cue(a)
  -- "cue" = ancien nom interne, encore accepté le temps de la migration
  return a and (a.type == "audio")
end
function X.is_region_cue(a)
  return a and a.type == "region"
end

-- Migration + normalisation d'une action chargée / collée.
function X.normalize_action(a)
  if not a or type(a) ~= "table" then return a end
  -- Ancien format : type "cue" + src "region" → type region
  if a.type == "cue" and a.src == "region" then
    a.type = "region"
  end
  -- Ancien type fichier "cue" → "audio"
  if a.type == "cue" then
    a.type = "audio"
  end
  if a.type == "snapshot" then
    a.type = "snapshot"
  end
  if a.type == "region" then
    a.src = "region"
  elseif a.type == "audio" then
    a.src = "file"
  end
  return a
end

function X.track_combo(label, guid, allow_none)
  local tr = X.find_track(guid)
  local preview = tr and X.track_name(tr) or (allow_none and "(piste d'origine)" or "(choisir)")
  local changed, new = false, guid
  if reaper.ImGui_BeginCombo(ctx, label, preview) then
    if allow_none and reaper.ImGui_Selectable(ctx, "(piste d'origine)##none", guid == nil) then
      new, changed = nil, true
    end
    for i = 0, reaper.CountTracks(PROJ)-1 do
      local t = reaper.GetTrack(PROJ, i)
      local g = reaper.GetTrackGUID(t)
      local folder = reaper.GetMediaTrackInfo_Value(t, "I_FOLDERDEPTH") == 1 and " [dossier]" or ""
      if reaper.ImGui_Selectable(ctx, (i+1)..". "..X.track_name(t)..folder.."##"..g, g == guid) then
        new, changed = g, true
      end
    end
    reaper.ImGui_EndCombo(ctx)
  end
  return changed, new
end

X.default_track_guid = function()
  -- Destination par défaut : première piste EXISTANTE du projet.
  -- Ne jamais créer de piste automatiquement lors de l'import ou du lancement.
  local tr = reaper.GetTrack(PROJ, 0)
  if tr then return reaper.GetTrackGUID(tr) end
  return nil
end

function X.add_action(t)
  local names = {audio="Audio", region="Region", snapshot="Snapshot", stop="Stop cues", pause="Pause", devamp="Devamp", osc="OSC", midi="MIDI"}
  local a = {id = next_id, type = t, name = names[t].." "..next_id}
  if t == "audio" or t == "cue" then
    a.type = "audio"
    a.src = "file"; a.fadein = 0; a.track = X.default_track_guid()
  end
  if t == "region" then
    a.src = "region"; a.fadein = 0; a.track = nil; a.copy = false
  end
  if t == "stop" then a.dur = 0.0 end
  if t == "pause" then a.dur = 0.5; a.unpause = false end
  if t == "snapshot" then
    a.type = "snapshot"
    a.dur = 0.0; a.use = {vol=true, pan=true, mute=true, solo=true, arm=true, fxen=true, fxpar=true, send=true}
  end
  if t == "osc" then a.port_name = ""; a.address = "/"; a.args = {} end
  if t == "midi" then
    a.midi_type = "note"; a.channel = 1
    a.note = 60; a.velocity = 100; a.cc = 1; a.value = 0; a.program = 0
  end
  next_id = next_id + 1
  local pos = #actions + 1
  for i, x in ipairs(actions) do if x.id == selected then pos = i + 1 end end
  table.insert(actions, pos, a)
  X.pick_only(a, pos)
  X.save()
end

---------------------------------------------------------------- Snap editor
function X.draw_snap_editor(a, lib)
  lib = lib or PROJ
  X.ensure_snap(a)
  a.use = a.use or {vol=true, pan=true, mute=true, solo=true, arm=true, fxen=true, fxpar=true, send=true}
  if a.use.send == nil then a.use.send = true end
  if lib ~= PROJ then
    local label = "projet cible"
    local src_fn = (a.type == "snapshot") and a.projfn or a.snap_projfn
    if src_fn and src_fn ~= "" then
      label = src_fn:match("([^/\\]+)$") or src_fn
    end
    reaper.ImGui_TextDisabled(ctx, "Pistes ciblées dans : " .. label)
  end
  if reaper.ImGui_Button(ctx, "Capturer les pistes sélectionnées") then
    local n = reaper.CountSelectedTracks(lib)
    if n == 0 then
      status = "Sélectionne d'abord une ou plusieurs pistes dans REAPER (projet cible)."
    else
      local snap = {order={}, tracks={}}
      for k = 0, n-1 do X.snap_add(snap, reaper.GetSelectedTrack(lib, k)) end
      a.snap = snap
      X.save()
      status = n.." piste(s) capturée(s)."
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Capturer toutes les pistes") then
    local snap = {order={}, tracks={}}
    for k = 0, reaper.CountTracks(lib)-1 do X.snap_add(snap, reaper.GetTrack(lib, k)) end
    a.snap = snap
    X.save()
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
      if x then X.save() end
    end
    reaper.ImGui_Spacing(ctx)
    reaper.ImGui_Text(ctx, "Ce que le snapshot rappelle :")
    local u = a.use
    local x
    x, u.vol   = reaper.ImGui_Checkbox(ctx, "Volume", u.vol)   ; if x then X.save() end
    reaper.ImGui_SameLine(ctx)
    x, u.pan   = reaper.ImGui_Checkbox(ctx, "Pan", u.pan)     ; if x then X.save() end
    reaper.ImGui_SameLine(ctx)
    x, u.mute  = reaper.ImGui_Checkbox(ctx, "Mute", u.mute)   ; if x then X.save() end
    reaper.ImGui_SameLine(ctx)
    x, u.solo  = reaper.ImGui_Checkbox(ctx, "Solo", u.solo)   ; if x then X.save() end
    reaper.ImGui_SameLine(ctx)
    x, u.arm   = reaper.ImGui_Checkbox(ctx, "Armer", u.arm)   ; if x then X.save() end
    reaper.ImGui_SameLine(ctx)
    x, u.fxen  = reaper.ImGui_Checkbox(ctx, "FX actif/bypass", u.fxen) ; if x then X.save() end
    reaper.ImGui_SameLine(ctx)
    x, u.fxpar = reaper.ImGui_Checkbox(ctx, "Paramètres FX", u.fxpar) ; if x then X.save() end
    reaper.ImGui_SameLine(ctx)
    if u.send == nil then u.send = true end
    x, u.send  = reaper.ImGui_Checkbox(ctx, "Sends", u.send) ; if x then X.save() end
    if reaper.ImGui_TreeNode(ctx, "Détail des effets##fxdetail") then
      for _, g in ipairs(a.snap.order) do
        local st = a.snap.tracks[g]
        if #(st.fx or {}) > 0 then
          reaper.ImGui_Text(ctx, st.name or "?")
          for k, f in ipairs(st.fx) do
            local y
            y, f.use = reaper.ImGui_Checkbox(ctx,
              k..". "..f.name..(f.enabled and " (actif)" or " (bypass)").."##fx"..g..k, f.use)
            if y then X.save() end
          end
        end
      end
      reaper.ImGui_TreePop(ctx)
    end
  end
end

---------------------------------------------------------------- Forme d'onde
X.DB_MIN, X.DB_MAX = -60, 12
X.C_LEFT, X.C_RIGHT = reaper.ImGui_MouseButton_Left(), reaper.ImGui_MouseButton_Right()

-- Construit réellement les peaks REAPER : l'API fonctionne en trois phases
-- (Begin, Run jusqu'à 0, Finish). Détruire la source juste après Begin ne suffit pas.
function X.build_peaks_file(file)
  if not file or file == "" then return false, "Aucun fichier audio." end
  if not reaper.PCM_Source_BuildPeaks then
    return false, "PCM_Source_BuildPeaks n'est pas disponible dans cette version de REAPER."
  end
  local src = reaper.PCM_Source_CreateFromFile(file)
  if not src then return false, "REAPER ne peut pas ouvrir la source audio : " .. tostring(file) end

  local ok, remaining = pcall(reaper.PCM_Source_BuildPeaks, src, 0)
  if not ok then
    reaper.PCM_Source_Destroy(src)
    return false, "Échec au démarrage de la génération des peaks."
  end

  if type(remaining) == "number" and remaining > 0 then
    local iterations = 0
    while remaining > 0 and iterations < 100000 do
      local run_ok, next_remaining = pcall(reaper.PCM_Source_BuildPeaks, src, 1)
      if not run_ok or type(next_remaining) ~= "number" then
        reaper.PCM_Source_Destroy(src)
        return false, "Échec pendant la génération des peaks."
      end
      remaining = next_remaining
      iterations = iterations + 1
    end
    if remaining > 0 then
      reaper.PCM_Source_Destroy(src)
      return false, "La génération des peaks n'a pas terminé dans le délai prévu."
    end
    local finish_ok = pcall(reaper.PCM_Source_BuildPeaks, src, 2)
    if not finish_ok then
      reaper.PCM_Source_Destroy(src)
      return false, "Échec de finalisation du fichier peaks."
    end
  end
  reaper.PCM_Source_Destroy(src)
  wave_cache[file] = nil
  return true
end

function X.rebuild_wave_peaks(file)
  return X.build_peaks_file(file)
end

function X.get_wave(file)
  local w = wave_cache[file]
  if w then return w end
  w = {views = {}}
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
  -- Aperçu global (zoom 1×) : résolution de base plus élevée.
  local N = 4096
  local buf = reaper.new_array(N * nch * 2)
  buf.clear()
  local ret = reaper.PCM_Source_GetPeaks(src, N / len, 0, nch, N, 0, buf)
  local cnt = math.floor(ret) & 0xFFFFF
  if cnt <= 0 and reaper.PCM_Source_BuildPeaks then
    -- Certains médias ajoutés par ReaLive n'ont pas encore de peaks. Demander
    -- une reconstruction, puis refaire la lecture des peaks une fois.
    pcall(reaper.PCM_Source_BuildPeaks, src, 0, true)
    buf.clear()
    ret = reaper.PCM_Source_GetPeaks(src, N / len, 0, nch, N, 0, buf)
    cnt = math.floor(ret) & 0xFFFFF
  end
  reaper.PCM_Source_Destroy(src)
  if cnt <= 0 then w.err = "Forme d'onde indisponible : REAPER n'a pas fourni de peaks après tentative de reconstruction." return w end
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

-- Peaks pour la fenêtre visible uniquement : plus on zoom, plus le détail augmente.
function X.get_wave_view(file, t0, t1, n_samples)
  local w = X.get_wave(file)
  if not w or w.err or not w.len then return nil end
  n_samples = math.max(64, math.min(8192, math.floor(n_samples + 0.5)))
  t0 = math.max(0, t0 or 0)
  t1 = math.min(w.len, t1 or w.len)
  if t1 <= t0 + 1e-9 then return nil end
  local key = string.format("%.5f|%.5f|%d", t0, t1, n_samples)
  w.views = w.views or {}
  local cached = w.views[key]
  if cached then return cached end
  -- Limiter le nombre d'entrées de cache de vues.
  local nkeys = 0
  for _ in pairs(w.views) do nkeys = nkeys + 1 end
  if nkeys > 24 then w.views = {} end
  local src = reaper.PCM_Source_CreateFromFile(file)
  if not src then return nil end
  local nch = math.max(1, math.min(2, w.nch_full or 1))
  local span = t1 - t0
  local peakrate = n_samples / span
  local buf = reaper.new_array(n_samples * nch * 2)
  buf.clear()
  local ret = reaper.PCM_Source_GetPeaks(src, peakrate, t0, nch, n_samples, 0, buf)
  reaper.PCM_Source_Destroy(src)
  local cnt = math.floor(ret) & 0xFFFFF
  if cnt <= 0 then return nil end
  local vmaxs, vmins = {}, {}
  for sidx = 1, cnt do
    local mx, mn = -1, 1
    for c = 0, nch-1 do
      local vmax = buf[(sidx-1)*nch + c + 1]
      local vmin = buf[n_samples*nch + (sidx-1)*nch + c + 1]
      if vmax > mx then mx = vmax end
      if vmin < mn then mn = vmin end
    end
    vmaxs[sidx] = math.max(-1, math.min(1, mx))
    vmins[sidx] = math.max(-1, math.min(1, mn))
  end
  cached = {max = vmaxs, min = vmins, n = cnt, t0 = t0, t1 = t1}
  w.views[key] = cached
  return cached
end

function X.g_to_frac(g)
  local db = (g <= 0.001) and X.DB_MIN or 20 * math.log(g, 10)
  db = math.max(X.DB_MIN, math.min(X.DB_MAX, db))
  return (db - X.DB_MIN) / (X.DB_MAX - X.DB_MIN)
end

function X.frac_to_g(f)
  f = math.max(0, math.min(1, f))
  local db = X.DB_MIN + f * (X.DB_MAX - X.DB_MIN)
  if db <= X.DB_MIN + 0.5 then return 0 end
  if math.abs(db) < 0.7 then return 1 end
  return 10 ^ (db / 20)
end

function X.apply_cue_changes(a)
  if X.is_file_cue(a) and runs[a.id] and runs[a.id].loop then
    X.replan_loop_run(a, runs[a.id])
    return
  end
  if X.is_file_cue(a) and runs[a.id] then
    local r = runs[a.id]
    r.tin = a.inpt
    r.seg = a.outpt - a.inpt
    r.speed = X.cue_effective_speed(a, X.now_pos())
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
        local pnow = X.now_pos()
        local elapsed = math.max(0, pnow - (r.t0 or pnow))
        local rel = r.loop and (r.proj_seg > 0 and (elapsed % r.proj_seg) or 0) or math.min(elapsed, r.proj_seg)
        local gain = X.cue_vol(a.id, r.env, r.tin + rel * r.speed)
        reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", gain)
        local dest = X.find_track(r.dest_guid)
        if dest then
          for ii = 0, reaper.CountTrackMediaItems(dest) - 1 do
            local other = reaper.GetTrackMediaItem(dest, ii)
            local _, cid = reaper.GetSetMediaItemInfo_String(other, "P_EXT:cuelist_id", "", false)
            if cid == tostring(a.id) then
              local otk = reaper.GetActiveTake(other)
              if otk then
                local opos = reaper.GetMediaItemInfo_Value(other, "D_POSITION")
                local olen = reaper.GetMediaItemInfo_Value(other, "D_LENGTH")
                -- On conserve la portion de source de chaque item (reprise après pause…) :
                -- seule la durée projet suit la vitesse.
                local orate = reaper.GetMediaItemTakeInfo_Value(otk, "D_PLAYRATE")
                if orate and orate > 0 and math.abs(orate - r.speed) > 1e-9 then
                  reaper.SetMediaItemInfo_Value(other, "D_LENGTH", math.max(0.001, olen * orate / r.speed))
                  reaper.SetMediaItemTakeInfo_Value(otk, "D_PLAYRATE", r.speed)
                end
                local oso = reaper.GetMediaItemTakeInfo_Value(otk, "D_STARTOFFS") or r.tin
                local local_t = oso + math.max(0, pnow - opos) * r.speed
                reaper.SetMediaItemTakeInfo_Value(otk, "D_VOL", X.cue_vol(a.id, r.env, local_t))
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

function X.assign_audio_file(a, f)
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
  -- Précharger la waveform dès l'assignation : si les peaks manquent, X.get_wave
  -- demande leur reconstruction au moteur REAPER au lieu d'attendre un geste manuel.
  local initial_wave = X.get_wave(f)
  if initial_wave and initial_wave.err then
    status = "Fichier chargé, mais waveform indisponible : " .. tostring(initial_wave.err)
  end
  X.save()
end

-- Gestion des chemins, récupération des médias et sauvegarde Bundle.
function X.path_join(a, b)
  if not a or a == "" then return b or "" end
  if not b or b == "" then return a end
  return (a:gsub("[\\/]+$", "") .. "/" .. b:gsub("^[\\/]+", ""))
end

function X.path_dir(path)
  path = (path or ""):gsub("\\", "/")
  return path:match("^(.*)/[^/]*$") or ""
end

function X.path_base(path)
  path = (path or ""):gsub("\\", "/")
  return path:match("([^/]+)$") or path
end

function X.path_is_absolute(path)
  path = tostring(path or "")
  return path:match("^%a:[/\\]") ~= nil or path:match("^[/\\][/\\]") ~= nil or path:match("^/") ~= nil
end

function X.file_exists(path)
  if not path or path == "" then return false end
  if reaper.file_exists then
    local ok, exists = pcall(reaper.file_exists, path)
    if ok and exists then return true end
  end
  local f = io.open(path, "rb")
  if f then f:close(); return true end
  return false
end

function X.copy_file(src, dst)
  local input = io.open(src, "rb")
  if not input then return false, "Lecture impossible : " .. tostring(src) end
  local output = io.open(dst, "wb")
  if not output then input:close(); return false, "Écriture impossible : " .. tostring(dst) end
  while true do
    local chunk = input:read(1024 * 1024)
    if not chunk then break end
    local ok, err = output:write(chunk)
    if not ok then input:close(); output:close(); return false, err or "Écriture interrompue." end
  end
  input:close(); output:close()
  return true
end

function X.walk_find_by_name(root, wanted, results, visited)
  if not reaper.EnumerateFiles or not reaper.EnumerateSubdirectories then return end
  results, visited = results or {}, visited or {}
  local key = tostring(root):lower()
  if visited[key] then return results end
  visited[key] = true
  local i = 0
  while true do
    local name = reaper.EnumerateFiles(root, i)
    if not name then break end
    if name:lower() == wanted:lower() then results[#results+1] = X.path_join(root, name) end
    i = i + 1
  end
  i = 0
  while true do
    local name = reaper.EnumerateSubdirectories(root, i)
    if not name then break end
    X.walk_find_by_name(X.path_join(root, name), wanted, results, visited)
    i = i + 1
  end
  return results
end

function X.resolve_loaded_media_paths(actionlist_path)
  local base = X.path_dir(actionlist_path)
  local missing = {}
  for _, tab in ipairs(tabs or {}) do
    for _, a in ipairs(tab.actions or {}) do
      if type(a.file) == "string" and a.file ~= "" then
        if not X.path_is_absolute(a.file) then
          local candidate = X.path_join(base, a.file)
          if X.file_exists(candidate) then a.file = candidate end
        end
        if not X.file_exists(a.file) then missing[#missing+1] = a end
      end
    end
  end
  if #missing == 0 then return 0 end

  local root = nil
  if reaper.JS_Dialog_BrowseForFolder then
    local ok, folder = reaper.JS_Dialog_BrowseForFolder(
      string.format("%d fichier(s) audio manquant(s) — choisir le dossier de recherche", #missing), base)
    if ok and folder and folder ~= "" then root = folder end
  end
  local repaired, ambiguous = 0, 0
  if root then
    for _, a in ipairs(missing) do
      local found = X.walk_find_by_name(root, X.path_base(a.file), {})
      if #found == 1 then
        a.file = found[1]; wave_cache[a.file] = nil; repaired = repaired + 1
      elseif #found > 1 then
        ambiguous = ambiguous + 1
        if reaper.GetUserFileNameForRead then
          local ok, chosen = reaper.GetUserFileNameForRead(found[1], "Plusieurs fichiers nommés " .. X.path_base(a.file) .. " — choisir le bon", "")
          if ok and chosen and chosen ~= "" and X.file_exists(chosen) then
            a.file = chosen; wave_cache[a.file] = nil; repaired = repaired + 1
          end
        end
      end
    end
  end
  local still_missing = 0
  for _, a in ipairs(missing) do if not X.file_exists(a.file) then still_missing = still_missing + 1 end end
  if still_missing > 0 then
    status = string.format("ActionList ouverte : %d média(s) manquant(s), %d réparé(s). Utilise Open après avoir regroupé les médias pour relancer la recherche.", still_missing, repaired)
  else
    status = string.format("ActionList ouverte : tous les médias retrouvés (%d chemin(s) corrigé(s)).", repaired)
  end
  return still_missing
end

function X.save_bundle(folder, lua_filename)
  if not folder or folder == "" then return false, "Dossier Bundle non sélectionné." end
  if not reaper.RecursiveCreateDirectory then return false, "Cette version de REAPER ne permet pas de créer le dossier Bundle." end
  local root = folder:gsub("[\\/]+$", "")
  reaper.RecursiveCreateDirectory(root, 0)
  local audio_dir = X.path_join(root, "audiofiles")
  reaper.RecursiveCreateDirectory(audio_dir, 0)
  local test_path = X.path_join(root, ".realive_bundle_write_test.tmp")
  local test = io.open(test_path, "wb")
  if not test then return false, "Impossible d'écrire dans le dossier Bundle." end
  test:close(); os.remove(test_path)

  local data = {actions = actions, tabs = tabs, active_tab = active_tab, next_id = next_id, prefs = prefs}
  local loader = load("return " .. X.ser(data), "bundle_copy", "t", {})
  if not loader then return false, "Impossible de préparer une copie de l'ActionList." end
  local ok_clone, clone = pcall(loader)
  if not ok_clone or type(clone) ~= "table" then return false, "Impossible de préparer une copie de l'ActionList." end
  local copied, peaks_copied, peaks_missing, path_map, used_names = 0, 0, 0, {}, {}
  local function copy_action_list(list)
    for _, a in ipairs(list or {}) do
      if type(a.file) == "string" and a.file ~= "" then
        local original = a.file
        if not X.file_exists(original) then return false, "Média introuvable : " .. original end
        local rel = path_map[original]
        if not rel then
          local name = X.path_base(original)
          local stem, ext = name:match("^(.*)(%.[^%.]+)$")
          stem, ext = stem or name, ext or ""
          local candidate, n = name, 2
          while used_names[candidate:lower()] do
            candidate = stem .. "_" .. tostring(n) .. ext; n = n + 1
          end
          used_names[candidate:lower()] = true
          rel = "audiofiles/" .. candidate
          local destination = X.path_join(audio_dir, candidate)
          local ok, err = X.copy_file(original, destination)
          if not ok then return false, err end

          -- Priorité à la copie du cache existant. Si le cache n'est pas
          -- adjacent au média ou si la copie échoue, générer les peaks sur la
          -- COPIE du média dans audiofiles : c'est ce chemin que REAPER ouvrira.
          local source_peaks = original .. ".reapeaks"
          local destination_peaks = destination .. ".reapeaks"
          local peaks_ok = false
          if X.file_exists(source_peaks) then
            peaks_ok = X.copy_file(source_peaks, destination_peaks) == true
          end
          if not peaks_ok and X.build_peaks_file then
            local built = X.build_peaks_file(destination)
            peaks_ok = built == true and X.file_exists(destination_peaks)
          end
          if peaks_ok then
            peaks_copied = peaks_copied + 1
          else
            peaks_missing = peaks_missing + 1
          end
          path_map[original] = rel; copied = copied + 1
        end
        a.file = rel
      end
    end
    return true
  end
  local ok, err = true, nil
  if type(clone.tabs) == "table" then
    for _, tab in ipairs(clone.tabs) do ok, err = copy_action_list(tab.actions); if not ok then break end end
    -- Le format historique sérialise aussi `actions` séparément ; au chargement,
    -- l'onglet actif est réassigné depuis ce champ. Le faire pointer vers la copie
    -- modifiée évite que les chemins absolus d'origine écrasent les chemins Bundle.
    if ok and clone.tabs[clone.active_tab] then clone.actions = clone.tabs[clone.active_tab].actions end
  else
    ok, err = copy_action_list(clone.actions)
  end
  if not ok then return false, err end
  local output_name = (lua_filename and lua_filename ~= "") and X.path_base(lua_filename) or "ActionList.lua"
  if not output_name:lower():match("%.lua$") then output_name = output_name .. ".lua" end
  local output_path = X.path_join(root, output_name)
  local out = io.open(output_path, "w")
  if not out then return false, "Impossible d'enregistrer " .. output_name .. " dans le Bundle." end
  out:write(X.ser(clone)); out:close()
  local summary = string.format("Bundle créé : %s (fichier %s, %d fichier(s) audio copié(s), %d fichier(s) .reapeaks copié(s)).", root, output_name, copied, peaks_copied)
  if peaks_missing > 0 then
    summary = summary .. string.format(" Attention : %d fichier(s) .reapeaks absent(s) ou non copié(s) ; REAPER devra les régénérer.", peaks_missing)
  end
  return true, summary
end

-- ReaImGui 0.1.x supports native file-drop payloads. Call this only directly
-- after an ImGui item (for example an InvisibleButton) has been submitted.
function X.accept_audio_file_drop(a)
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
      X.assign_audio_file(a, chosen)
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
function X.accept_audio_file_drop_create(insert_index)
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
      local guid = X.default_track_guid()
      local pos = math.max(1, math.min(#actions + 1, (insert_index or #actions) + 1))
      local first_pos, new_ids = pos, {}
      for _, chosen in ipairs(files) do
        local base = chosen:gsub("\\", "/"):match("([^/]+)$") or chosen
        base = base:gsub("%.[^%.]+$", "")
        local a = {id=next_id, type="audio", name=base, src="file", file=chosen,
          track=guid, fadein=0, inpt=0, outpt=nil, env=nil, markers={}, marker_name="Q1",
          view_zoom=1.0, view_offset=0.0}
        next_id = next_id + 1
        table.insert(actions, pos, a)
        X.assign_audio_file(a, chosen)
        new_ids[#new_ids+1] = a.id
        pos = pos + 1
      end
      -- Tout le lot est sélectionné ; la première cue est la cue préparée / éditée.
      picked = {}
      for _, id in ipairs(new_ids) do picked[id] = true end
      pick_anchor = first_pos
      selected = new_ids[1]
      X.save()
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

-- Active/désactive le reverse natif REAPER en enveloppant la source dans SOURCE SECTION.
-- B_REVERSE n'est pas un attribut Take valide de l'API : le régler ne change donc rien.
function X.set_item_reverse(item, reverse)
  if not item or not reaper.GetItemStateChunk or not reaper.SetItemStateChunk then return false end
  local ok, chunk = reaper.GetItemStateChunk(item, "", false)
  if not ok or type(chunk) ~= "string" or chunk == "" then return false end

  local source_start = chunk:find("<SOURCE SECTION", 1, true)
  if source_start then
    -- Déjà en SECTION : on conserve la source imbriquée et ne change que MODE.
    local inner_start = chunk:find("<SOURCE WAVE", source_start, true)
    if not inner_start then
      -- Sources autres que WAVE : ne pas toucher à une structure inconnue.
      return false
    end
    local inner_end = chunk:find("\n>", inner_start, true)
    if not inner_end then return false end
    local section_end = chunk:find("\n>", inner_end + 2, true)
    if not section_end then return false end
    local section = chunk:sub(source_start, section_end + 1)
    if reverse then
      local updated, n = section:gsub("MODE%s+[%-%d]+", "MODE 3", 1)
      if n == 0 then updated = updated:gsub("(<SOURCE SECTION[^\n]*\n)", "%1LENGTH 0.000\nMODE 3\nSTARTPOS 0.000\nOVERLAP 0.010\n", 1) end
      chunk = chunk:sub(1, source_start - 1) .. updated .. chunk:sub(section_end + 2)
    else
      -- Retire le wrapper SECTION et remet la source WAVE à sa place.
      local inner = chunk:sub(inner_start, inner_end + 1)
      chunk = chunk:sub(1, source_start - 1) .. inner .. chunk:sub(section_end + 2)
    end
  elseif reverse then
    local wave_start = chunk:find("<SOURCE WAVE", 1, true)
    if not wave_start then return false end
    local wave_end = chunk:find("\n>", wave_start, true)
    if not wave_end then return false end
    local wave = chunk:sub(wave_start, wave_end + 1)
    local wrapper = "<SOURCE SECTION\nLENGTH 0.000\nMODE 3\nSTARTPOS 0.000\nOVERLAP 0.010\n" .. wave .. "\n>"
    chunk = chunk:sub(1, wave_start - 1) .. wrapper .. chunk:sub(wave_end + 2)
  else
    return true -- déjà en lecture normale
  end
  local set_ok = reaper.SetItemStateChunk(item, chunk, false)
  if set_ok then reaper.UpdateItemInProject(item) end
  return set_ok
end

function X.apply_wave_cue_props(a)
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
          reaper.SetMediaItemTakeInfo_Value(tk, "D_VOL", X.cue_vol(a.id, a.env, startoffs))
          reaper.SetMediaItemTakeInfo_Value(tk, "D_PAN", pan)
          local old_rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE")
          if not old_rate or old_rate <= 0 then old_rate = 1 end
          local old_len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
          local item_pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
          local effective_speed, tempo_ratio = X.cue_effective_speed(a, item_pos)
          reaper.SetMediaItemTakeInfo_Value(tk, "D_PLAYRATE", effective_speed)
          reaper.SetMediaItemTakeInfo_Value(tk, "D_PITCH", pitch)
          reaper.SetMediaItemTakeInfo_Value(tk, "B_PPITCH", (a.wave_stretch_tempo and tempo_ratio ~= 1) and 1 or 0)
          X.set_item_reverse(it, a.wave_reverse)
          -- L'étirement au tempo est calculé explicitement depuis le BPM source.
          -- C_AUTOSTRETCH reste désactivé pour éviter les artefacts sur les items internes.
          reaper.SetMediaItemInfo_Value(it, "C_BEATATTACHMODE", 0)
          reaper.SetMediaItemInfo_Value(it, "C_AUTOSTRETCH", 0)
          -- Conserver la portion de source de l'item : la durée projet suit la vitesse effective.
          reaper.SetMediaItemInfo_Value(it, "D_LENGTH", math.max(0.001, old_len * old_rate / effective_speed))
          reaper.UpdateItemInProject(it)
          changed = changed + 1
        end
      end
    end
  end
  if runs[a.id] then
    local r = runs[a.id]
    r.speed = X.cue_effective_speed(a, X.now_pos())
    r.seg = src_seg
    r.proj_seg = src_seg / r.speed
    if r.loop then X.replan_loop_run(a, r) end
  end
  if changed > 0 then reaper.UpdateArrange() end
end

-- Cues audio sélectionnées (par titre) dans tous les onglets, au format "Q1,Q8".
-- Réservé à STOP / Pause / Devamp : cues fichier et région retenues.
-- Actions sélectionnées (par titre) quel que soit le type (AUDIO, REGION, OSC, MIDI, SNAPSHOT…).
-- Utilisé uniquement pour la capture dans les marqueurs take.
function X.picked_any_names()
  local parts = {}
  for _, tab in ipairs(tabs or {}) do
    for _, x in ipairs(tab.actions or {}) do
      if picked[x.id] then parts[#parts+1] = "Q" .. tostring(x.id) end
    end
  end
  return table.concat(parts, ","), #parts
end

-- Les marqueurs Qx sont lus sur les TAKE MARKERS des items déjà posés sur la timeline :
-- après toute modification (nom, capture, position, ajout, suppression) il faut les
-- réécrire sur les items existants de la cue, sinon rien ne change à la lecture.
X.marker_sel, X.cap_n = {}, {}
function X.refresh_item_markers(a)
  if not (reaper.SetTakeMarker and reaper.GetNumTakeMarkers and reaper.DeleteTakeMarker) then return end
  local sid, n = tostring(a.id), 0
  for i = 0, reaper.CountMediaItems(PROJ) - 1 do
    local it = reaper.GetMediaItem(PROJ, i)
    local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
    if cid == sid then
      local tk = reaper.GetActiveTake(it)
      if tk and not reaper.TakeIsMIDI(tk) then
        for m = reaper.GetNumTakeMarkers(tk) - 1, 0, -1 do reaper.DeleteTakeMarker(tk, m) end
        local so = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS") or 0
        local rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE")
        if not rate or rate <= 0 then rate = 1 end
        local se = so + reaper.GetMediaItemInfo_Value(it, "D_LENGTH") * rate
        for _, marker in ipairs(a.markers or {}) do
          local mt = tonumber(marker.t)
          local mn = tostring(marker.name or ""):gsub("^%s+", ""):gsub("%s+$", "")
          if mt and mn ~= "" and mt >= so - 1e-6 and mt <= se + 1e-6 then
            reaper.SetTakeMarker(tk, -1, mn, mt, tonumber(marker.color) or 0)
          end
        end
        reaper.UpdateItemInProject(it)
        n = n + 1
      end
    end
  end
  return n
end

-- Réglages de lecture (gain / pan / vitesse / pitch) : section repliable,
-- placée en bas de l'éditeur de forme d'onde.
function X.draw_play_settings(a)
  reaper.ImGui_Separator(ctx)
  if reaper.ImGui_CollapsingHeader(ctx, "Réglages de lecture (gain, pan, vitesse, pitch, reverse, tempo)##playset", nil,
      reaper.ImGui_TreeNodeFlags_DefaultOpen()) then
    local cg, gain_db = reaper.ImGui_SliderDouble(ctx, "Gain (dB)##wave_gain", a.wave_gain_db, -60, 12, "%.1f dB")
    if cg then a.wave_gain_db = gain_db; X.apply_wave_cue_props(a); X.save() end
    local cp, pan = reaper.ImGui_SliderDouble(ctx, "Pan##wave_pan", a.wave_pan, -1, 1, "%.2f")
    if cp then a.wave_pan = pan; X.apply_wave_cue_props(a); X.save() end
    -- Mise en page en deux lignes : vitesse / pitch à gauche, options alignées à droite.
    reaper.ImGui_SetNextItemWidth(ctx, X.S(130))
    local cs, speed = reaper.ImGui_InputDouble(ctx, "Vitesse##wave_speed", a.wave_speed, 0.1, 0.5, "%.3f")
    if cs then a.wave_speed = math.max(0.01, math.min(16, speed)); X.apply_wave_cue_props(a); X.save() end
    reaper.ImGui_SameLine(ctx)
    local cst, stretch = reaper.ImGui_Checkbox(ctx, "Stretch au tempo##wave_stretch_tempo", a.wave_stretch_tempo)
    if cst then a.wave_stretch_tempo = stretch; X.apply_wave_cue_props(a); X.save() end

    if not a.wave_pitch_link then
      reaper.ImGui_SetNextItemWidth(ctx, X.S(130))
      local cpi, pitch = reaper.ImGui_InputDouble(ctx, "Pitch (demi-tons)##wave_pitch", a.wave_pitch, 1, 4, "%.2f")
      if cpi then a.wave_pitch = math.max(-48, math.min(48, pitch)); X.apply_wave_cue_props(a); X.save() end
    else
      reaper.ImGui_Text(ctx, "Pitch lié à la vitesse")
      reaper.ImGui_SameLine(ctx)
      local linked_pitch = 12 * (math.log(math.max(0.01, a.wave_speed)) / math.log(2))
      reaper.ImGui_TextDisabled(ctx, string.format("%+.2f demi-tons", linked_pitch))
    end
    reaper.ImGui_SameLine(ctx)
    local cr, reverse = reaper.ImGui_Checkbox(ctx, "Reverse##wave_reverse", a.wave_reverse)
    if cr then a.wave_reverse = reverse; X.apply_wave_cue_props(a); X.save() end

    -- Le lien hauteur/vitesse est placé sur la ligne sous l'option Stretch.
    reaper.ImGui_SetCursorPosX(ctx, X.S(205))
    local cl, linked = reaper.ImGui_Checkbox(ctx, "Lier la hauteur à la vitesse##wave_pitch_link", a.wave_pitch_link)
    if cl then a.wave_pitch_link = linked; X.apply_wave_cue_props(a); X.save() end
    reaper.ImGui_TextDisabled(ctx, "Stretch : BPM source requis (métadonnées ou nom du fichier, ex. 120bpm). Sans BPM détecté, la vitesse reste inchangée.")
    reaper.ImGui_TextDisabled(ctx, "Ces réglages sont propres à cette cue et s'appliquent à ses items REAPER existants et aux prochaines lectures.")
  end
end

function X.draw_wave_editor(a)
  if not a.file or a.file == "" then
    reaper.ImGui_TextDisabled(ctx, "Aucun fichier chargé. Glisse un fichier audio ou vidéo dans la zone ci-dessous.")
    if reaper.ImGui_Button(ctx, "Charger un fichier audio...##wave_load_empty") then
      local ok, f = reaper.GetUserFileNameForRead("", "Fichier audio", "")
      if ok and f ~= "" then X.assign_audio_file(a, f) end
    end
    local drop_w = math.max(X.S(260), select(1, reaper.ImGui_GetContentRegionAvail(ctx)) - X.S(8))
    reaper.ImGui_InvisibleButton(ctx, "##wave_drop_empty", drop_w, X.S(100))
    local dx, dy = reaper.ImGui_GetItemRectMin(ctx)
    local ex, ey = reaper.ImGui_GetItemRectMax(ctx)
    local ddl = reaper.ImGui_GetWindowDrawList(ctx)
    reaper.ImGui_DrawList_AddRect(ddl, dx, dy, ex, ey, 0xFF777777, 0, 0, X.S(1))
    reaper.ImGui_DrawList_AddText(ddl, dx + X.S(16), dy + X.S(38), 0xFFBBBBBB, "Déposer le fichier audio ici")
    X.accept_audio_file_drop(a)
    return
  end
  reaper.ImGui_Text(ctx, a.file)
  a.wave_gain_db = tonumber(a.wave_gain_db) or 0
  a.wave_pan = tonumber(a.wave_pan) or 0
  a.wave_speed = tonumber(a.wave_speed) or 1
  a.wave_pitch = tonumber(a.wave_pitch) or 0
  a.wave_pitch_link = a.wave_pitch_link and true or false
  a.wave_reverse = a.wave_reverse and true or false
  a.wave_stretch_tempo = a.wave_stretch_tempo and true or false
  if reaper.ImGui_Button(ctx, "Remplacer le fichier...##wave_replace") then
    local ok, f = reaper.GetUserFileNameForRead(a.file, "Remplacer le fichier audio", "")
    if ok and f ~= "" then X.assign_audio_file(a, f) end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Supprimer fichier##wave_clear") then
    a.file, a.inpt, a.outpt, a.env = nil, nil, nil, nil
    a.markers, a.marker_name = {}, "Q1"
    a.view_zoom, a.view_offset = 1.0, 0.0
    marker_drag, wf_drag, cv_drag = nil, nil, nil
    X.save()
    -- Le fichier vient d'être retiré : ne pas poursuivre le rendu de la waveform
    -- avec a.file == nil, sinon X.get_wave(nil) provoque « table index is nil ».
    return
  end
  reaper.ImGui_Separator(ctx)
  a.markers = type(a.markers) == "table" and a.markers or {}
  a.marker_name = a.marker_name or "Q1"
  local w = X.get_wave(a.file)
  if w.err then
    reaper.ImGui_Text(ctx, w.err)
    if reaper.ImGui_SmallButton(ctx, "Reconstruire la forme d'onde##wv") then
      local ok, msg = X.rebuild_wave_peaks(a.file)
      wave_cache[a.file] = nil
      if ok then
        status = "Reconstruction des peaks demandée à REAPER : " .. tostring(a.file)
      else
        status = msg or "REAPER n'a pas pu reconstruire les peaks."
      end
    end
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

  X.cap_n[a.id] = X.cap_n[a.id] or 0

  reaper.ImGui_SetNextItemWidth(ctx, X.S(90))
  local c1, v1 = reaper.ImGui_InputDouble(ctx, "Entrée (s)##in", a.inpt, 0, 0, "%.3f")
  if c1 then
    local old = a.inpt
    a.inpt = math.max(0, math.min(v1, a.outpt - 0.05))
    a.loop_in = math.max(a.inpt, math.min((a.loop_in or a.inpt) + (a.inpt - old), (a.loop_out or a.outpt) - 0.01))
    X.apply_cue_changes(a); X.save()
  end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_SetNextItemWidth(ctx, X.S(90))
  local c2, v2 = reaper.ImGui_InputDouble(ctx, "Sortie (s)##out", a.outpt, 0, 0, "%.3f")
  if c2 then
    local old = a.outpt
    a.outpt = math.max(a.inpt + 0.05, math.min(v2, L))
    a.loop_out = math.max((a.loop_in or a.inpt) + 0.01, math.min((a.loop_out or a.outpt) + (a.outpt - old), a.outpt))
    X.apply_cue_changes(a); X.save()
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_SmallButton(ctx, "Tout##full") then
    a.inpt, a.outpt, a.loop_in, a.loop_out = 0, L, 0, L
    X.apply_cue_changes(a); X.save()
  end

  local c3, lp = reaper.ImGui_Checkbox(ctx, "Boucle##loop", a.loop or false)
  if c3 then a.loop = lp; X.save() end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_SetNextItemWidth(ctx, X.S(50))
  local lc_str = a.loop_count and tostring(a.loop_count) or ""
  local clc, lc_val = reaper.ImGui_InputText(ctx, "×##loopcnt", lc_str)
  if clc then
    local n = tonumber(lc_val)
    a.loop_count = (n and n > 0) and math.floor(n) or nil
    X.save()
  end
  reaper.ImGui_SameLine(ctx)
  do
    local run = runs[a.id]
    local dev = run and (run.devamp or run.devamp_armed or devamp_flags[a.id])
    -- Clignote tant que la playhead n'a pas franchi Lo (process_runs coupe le flag).
    -- Nombre de boucles renseigné : clignote pendant la DERNIÈRE boucle (Li→Lo),
    -- pour signaler que la suite Lo→OUT va s'enchaîner toute seule.
    if run and run.alive and not run.paused and run.loop and run.loop_count
       and run.phase == "release" and run.release_start and run.lo and run.li then
      local cyc = math.max(0.001, run.lo - run.li) / math.max(0.01, run.speed or 1)
      local pp = X.now_pos()
      if pp >= run.release_start - cyc - 1e-3 and pp < run.release_start then dev = true end
    end
    if run and run.paused then dev = false end
    local blink = dev and (math.floor(reaper.time_precise() * 3) % 2 == 0)
    if blink then
      reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Button(), 0xE74C3CFF)
      reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_ButtonHovered(), 0xC0392BFF)
    end
    if reaper.ImGui_SmallButton(ctx, "Devamp##devamp") then
      if X.devamp_run(a.id) then
        -- statut posé par devamp_run
      elseif run and (run.devamp or run.devamp_armed) then
        status = "Devamp déjà armé."
      else
        status = "Devamp : lance d'abord la cue en boucle."
      end
    end
    if blink then reaper.ImGui_PopStyleColor(ctx, 2) end
  end
  reaper.ImGui_SameLine(ctx)
  do
    local run = runs[a.id]
    local paused = run and run.paused
    local label = paused and "Reprendre##wave_pause" or "Pause##wave_pause"
    if reaper.ImGui_SmallButton(ctx, label) then
      if run and run.alive then
        if not run.paused then X.pause_run(a.id, 0) else X.resume_run(a.id, 0) end
      else
        status = "Pause : aucune lecture en cours pour cette cue."
      end
    end
  end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_TextDisabled(ctx, string.format("fichier %.2f s  |  IN→OUT %.2f s  |  Li→Lo %.2f s",
    L, a.outpt - a.inpt, a.loop_out - a.loop_in))

  local avail_w = select(1, reaper.ImGui_GetContentRegionAvail(ctx))
  local cw = math.max(X.S(240), avail_w - X.S(8))
  
  local hb, hw = X.S(28), X.S(240) -- bande haute : IN/OUT + Li/Lo empilés
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
  local function ycv(g) return yb1 - X.g_to_frac(g) * hw end
  local xin, xout = tx(a.inpt), tx(a.outpt)
  local xli, xlo = tx(a.loop_in), tx(a.loop_out)

  local play_t
  local run = runs[a.id]
  if run and (X.is_playing() or run.paused) then
    play_t = X.run_source_time(run, X.now_pos())
  end

  reaper.ImGui_DrawList_AddRectFilled(dl, x0, y0, x0+cw, yb0, 0x24382CFF)
  reaper.ImGui_DrawList_AddRectFilled(dl, x0, yb0, x0+cw, yb1, 0x202020FF)

  -- Peaks adaptés à la fenêtre visible. En Reverse, on lit la fenêtre source
  -- miroir et on dessine ses colonnes de droite à gauche : seule la représentation
  -- est inversée, sans modifier le fichier audio ni les données de peaks en cache.
  local px_count = math.max(1, math.floor(cw))
  local reverse_wave = a.wave_reverse == true
  local peaks_t0 = reverse_wave and math.max(0, L - view_end) or view_x
  local peaks_t1 = reverse_wave and math.max(0, L - view_x) or view_end
  local view_peaks = X.get_wave_view(a.file, peaks_t0, peaks_t1, px_count)
  local mid = yb0 + hw/2
  if view_peaks and view_peaks.n and view_peaks.n > 0 then
    for px = 0, px_count - 1 do
      local col = math.floor((px / px_count) * (view_peaks.n - 1) + 0.5)
      local idx = reverse_wave and (view_peaks.n - col) or (1 + col)
      if idx < 1 then idx = 1 elseif idx > view_peaks.n then idx = view_peaks.n end
      local mxv, mnv = view_peaks.max[idx], view_peaks.min[idx]
      if mxv then
        local ya = mid - mxv * hw/2
        local yb = mid - mnv * hw/2
        if yb - ya < 1 then yb = ya + 1 end
        reaper.ImGui_DrawList_AddLine(dl, x0+px, ya, x0+px, yb, 0x4F7FA8FF)
      end
    end
  else
    -- Repli sur le cache global si l'échantillonnage local échoue.
    local idx_start, idx_end
    if reverse_wave then
      idx_start = math.max(1, math.floor(((L - view_end) / L) * w.n))
      idx_end = math.min(w.n, math.floor(((L - view_x) / L) * w.n))
    else
      idx_start = math.max(1, math.floor((view_x / L) * w.n))
      idx_end = math.min(w.n, math.floor((view_end / L) * w.n))
    end
    local idx_span = math.max(1, idx_end - idx_start)
    for px = 0, px_count - 1 do
      local offset = math.floor((px / px_count) * idx_span)
      local idx = reverse_wave and (idx_end - offset) or (idx_start + offset)
      local mxv, mnv = w.max[idx], w.min[idx]
      if mxv then
        local ya = mid - mxv * hw/2
        local yb = mid - mnv * hw/2
        if yb - ya < 1 then yb = ya + 1 end
        reaper.ImGui_DrawList_AddLine(dl, x0+px, ya, x0+px, yb, 0x4F7FA8FF)
      end
    end
  end

  for _, db in ipairs({-48, -36, -24, -12, 0}) do
    local yy = yb1 - ((db - X.DB_MIN)/(X.DB_MAX - X.DB_MIN)) * hw
    reaper.ImGui_DrawList_AddLine(dl, x0, yy, x0+cw, yy, db == 0 and 0x808040AA or 0x40404088, 1)
    reaper.ImGui_DrawList_AddText(dl, x0+3, yy - X.S(13), 0x909090FF, db.." dB")
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
      reaper.ImGui_DrawList_AddCircleFilled(dl, tx(math.max(a.inpt, math.min(a.outpt, pt.t))), ycv(pt.g), X.S(5), 0xFFFFFFFF)
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
  local tag_h = X.S(14)
  reaper.ImGui_DrawList_AddRectFilled(dl, xin, y0, xin + X.S(28), y0 + tag_h, 0x2ECC71FF)
  reaper.ImGui_DrawList_AddText(dl, xin + X.S(4), y0 + 1, 0x000000FF, "IN")
  reaper.ImGui_DrawList_AddRectFilled(dl, xout - X.S(34), y0, xout, y0 + tag_h, 0xE74C3CFF)
  reaper.ImGui_DrawList_AddText(dl, xout - X.S(30), y0 + 1, 0xFFFFFFFF, "OUT")

  -- Tags Li / Lo à LEUR position (bande haute, sous IN/OUT si coincidents sinon à xli/xlo)
  if show_loop_handles then
    reaper.ImGui_DrawList_AddRectFilled(dl, xli, y0 + tag_h, xli + X.S(26), y0 + tag_h * 2, 0xF39C12FF)
    reaper.ImGui_DrawList_AddText(dl, xli + X.S(4), y0 + tag_h + 1, 0x000000FF, "Li")
    reaper.ImGui_DrawList_AddRectFilled(dl, xlo - X.S(26), y0 + tag_h, xlo, y0 + tag_h * 2, 0xF39C12FF)
    reaper.ImGui_DrawList_AddText(dl, xlo - X.S(22), y0 + tag_h + 1, 0x000000FF, "Lo")
  end

  yend = yb1
  -- Curseur de lecture : uniquement dans la fenêtre visible, borné au rectangle waveform.
  if play_t and play_t >= view_x - 1e-9 and play_t <= view_end + 1e-9 then
    local px = tx(play_t)
    if px >= x0 - 1 and px <= x0 + cw + 1 then
      reaper.ImGui_DrawList_AddLine(dl, px, y0, px, yend, 0xFFFFFFFF, 2)
    end
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
      local label_h = X.S(24)
      local handle_h = X.S(10)
      
      reaper.ImGui_DrawList_AddLine(dl, mxm, yb0, mxm, yb1, edge, X.S(2))
      
      local tag_w = math.max(X.S(52), math.min(X.S(190), X.S(20) + #mn * X.S(8)))
      local label_x = math.max(x0, math.min(x0 + cw - tag_w, mxm - tag_w * 0.5))
      local lane = nil
      for l = 1, #lane_right do
        if label_x > lane_right[l] + X.S(3) then lane = l; break end
      end
      if not lane then lane = ((i - 1) % #lane_right) + 1 end
      lane_right[lane] = math.max(lane_right[lane], label_x + tag_w)
      
      local label_y = yb0 + X.S(1) + (lane - 1) * (label_h + X.S(2))
      local handle_top = label_y + label_h
      
      reaper.ImGui_DrawList_AddRectFilled(dl, mxm - X.S(6), handle_top, mxm + X.S(6), handle_top + handle_h, edge)
      reaper.ImGui_DrawList_AddRect(dl, mxm - X.S(6), handle_top, mxm + X.S(6), handle_top + handle_h, 0xFFFFFFFF, 0, 0, X.S(1))
      reaper.ImGui_DrawList_AddRectFilled(dl, label_x, label_y, label_x + tag_w, label_y + label_h, col)
      reaper.ImGui_DrawList_AddRect(dl, label_x, label_y, label_x + tag_w, label_y + label_h, edge, 0, 0, X.S(2))
      reaper.ImGui_DrawList_AddText(dl, label_x + X.S(7), label_y + X.S(4), 0xFFFFFFFF, mn)
      
      marker_boxes[#marker_boxes + 1] = {
        idx = i, x = mxm, left = label_x, right = label_x + tag_w,
        top = label_y, bottom = label_y + label_h + handle_h, color = col, name = mn
      }
    end
  end

  reaper.ImGui_SetCursorScreenPos(ctx, x0, y0)
  reaper.ImGui_InvisibleButton(ctx, "##inband", cw, hb)
  if reaper.ImGui_IsItemClicked(ctx, X.C_LEFT) then
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
  X.accept_audio_file_drop(a)
  local area_hover = reaper.ImGui_IsItemHovered(ctx)
  local mx, my = reaper.ImGui_GetMousePos(ctx)
  local body_hover = area_hover and my >= yb0 and my <= yb1

  -- Clic près des poignées Li/Lo en haut de la waveform → drag
  if area_hover and reaper.ImGui_IsItemClicked(ctx, X.C_LEFT) and show_loop_handles then
    local hsz = X.S(14)
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
    local wheel_h = 0
    if reaper.ImGui_GetMouseWheelH then
      wheel_h = reaper.ImGui_GetMouseWheelH(ctx) or 0
    end
    local is_ctrl = false
    if reaper.ImGui_GetKeyMods and reaper.ImGui_Mod_Ctrl then
      is_ctrl = (reaper.ImGui_GetKeyMods(ctx) & reaper.ImGui_Mod_Ctrl()) ~= 0
    else
      is_ctrl = reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftCtrl())
          or reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightCtrl())
    end
    local mouse_t = xt(mx)
    local view_changed = false
    -- Ctrl + molette verticale : zoom centré sous le curseur.
    if wheel ~= 0 and is_ctrl then
      local old_zoom = a.view_zoom
      a.view_zoom = math.max(1.0, math.min(80.0, old_zoom * (1 + wheel * 0.12)))
      local new_view_w = L / a.view_zoom
      local ratio = (mouse_t - view_x) / math.max(1e-9, view_w)
      a.view_offset = mouse_t - ratio * new_view_w
      view_changed = true
    end
    -- Molette horizontale : défilement gauche/droite (plus de Shift+molette verticale).
    if wheel_h ~= 0 then
      a.view_offset = a.view_offset + wheel_h * (view_w * 0.08)
      view_changed = true
    end
    if view_changed then
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
      if dx <= X.S(8) and dy <= X.S(8) then
        local d = dx * dx + dy * dy
        if not best_d or d < best_d then hit, best_d = i, d end
      end
    end
    return hit
  end

  local function hit_marker()
    local hit, best_d
    for _, box in ipairs(marker_boxes) do
      local in_label = mx >= box.left - X.S(3) and mx <= box.right + X.S(3)
        and my >= box.top - X.S(3) and my <= box.bottom + X.S(3)
      if in_label then
        local d = math.abs(mx - box.x)
        if not best_d or d < best_d then hit, best_d = box.idx, d end
      end
    end
    return hit
  end

  local clicked_left = reaper.ImGui_IsItemClicked(ctx, X.C_LEFT)
  local clicked_right = reaper.ImGui_IsItemClicked(ctx, X.C_RIGHT)
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

    if in_wave_body and clicked_left and ctrl and not alt then
      -- Ctrl + clic-glisser : naviguer (pan) dans la waveform zoomée.
      X.view_drag = {
        id = a.id,
        mx0 = mx,
        off0 = a.view_offset or 0,
        view_w = view_w,
        cw = cw
      }
      cv_drag, marker_drag, wf_drag = nil, nil, nil
      status = "Ctrl + glisser : navigation dans la forme d'onde."
    elseif in_wave_body and clicked_left and not alt and not ctrl then
      -- Clic normal = seek source, calé sur l'item de la cue sous la playhead (gère les boucles).
      local source_t = math.max(a.inpt, math.min(a.outpt, xt(mx)))
      local run = runs[a.id]
      if run and X.is_playing() then
        local speed = math.max(0.01, run.speed or tonumber(a.wave_speed) or 1)
        local project_t
        local dest = X.find_track(run.dest_guid)
        local pnow = X.now_pos()
        if dest then
          for i = reaper.CountTrackMediaItems(dest) - 1, 0, -1 do
            local it = reaper.GetTrackMediaItem(dest, i)
            local pos = reaper.GetMediaItemInfo_Value(it, "D_POSITION")
            local len = reaper.GetMediaItemInfo_Value(it, "D_LENGTH")
            if pos <= pnow and pos + len > pnow then
              local _, cid = reaper.GetSetMediaItemInfo_String(it, "P_EXT:cuelist_id", "", false)
              if cid == tostring(run.id) then
                local tk = reaper.GetActiveTake(it)
                if tk and not reaper.TakeIsMIDI(tk) then
                  local so = reaper.GetMediaItemTakeInfo_Value(tk, "D_STARTOFFS")
                  local rate = reaper.GetMediaItemTakeInfo_Value(tk, "D_PLAYRATE")
                  rate = (rate and rate > 0) and rate or speed
                  project_t = pos + (source_t - so) / rate
                  break
                end
              end
            end
          end
        end
        if not project_t then
          project_t = (tonumber(run.t0) or pnow)
            + (source_t - (tonumber(run.tin) or tonumber(a.inpt) or 0)) / speed
        end
        -- seekplay=true : déplace la tête de lecture en cours sans redémarrer le transport.
        reaper.SetEditCurPos2(PROJ, project_t, false, true)
        status = string.format("Lecture déplacée à %.3f s (source).", source_t)
      else
        status = "Clic : la cue doit être en lecture pour déplacer sa tête de lecture."
      end
      cv_drag, marker_drag = nil, nil
    elseif marker_hit then
      -- Clic droit = déplacer ; Alt+clic = supprimer.
      if clicked_right then
        marker_drag = {
          id = a.id, idx = marker_hit,
          offset = (tonumber(a.markers[marker_hit].t) or xt(mx)) - xt(mx),
          button = X.C_RIGHT
        }
        cv_drag = nil
        status = "Déplacement du marqueur " .. tostring(a.markers[marker_hit].name or "") .. "."
      elseif clicked_left and alt then
        local removed = table.remove(a.markers, marker_hit)
        marker_drag, cv_drag = nil, nil
        X.marker_sel[a.id] = nil
        X.refresh_item_markers(a)
        X.save()
        status = "Marqueur " .. tostring(removed and removed.name or "") .. " supprimé."
      end
    elseif in_wave_body and (alt or clicked_right) then
      if clicked_right then
        if curve_hit then table.remove(env, curve_hit); X.save() end
      elseif clicked_left and alt then
        marker_drag = nil
        local hit = curve_hit
        if not hit then
          local t = math.max(a.inpt, math.min(a.outpt, xt(mx)))
          table.insert(env, {t = t, g = X.frac_to_g(1 - (my - yb0)/hw)})
          table.sort(env, function(p,q) return p.t < q.t end)
          for i, pt in ipairs(env) do if pt.t == t then hit = i end end
        end
        cv_drag = hit and {idx = hit} or nil
      end
    end
  end

  -- Pan waveform : Ctrl + glisser horizontalement.
  if X.view_drag then
    if X.view_drag.id ~= a.id then
      X.view_drag = nil
    elseif reaper.ImGui_IsMouseDown(ctx, X.C_LEFT) then
      local dx = mx - X.view_drag.mx0
      local vw = X.view_drag.view_w or view_w
      local cww = math.max(1, X.view_drag.cw or cw)
      a.view_offset = (X.view_drag.off0 or 0) - (dx / cww) * vw
      a.view_offset = math.max(0, math.min(L - (L / (a.view_zoom or 1)), a.view_offset))
      view_w = L / a.view_zoom
      view_x = a.view_offset
      view_end = view_x + view_w
    else
      X.view_drag = nil
    end
  end

  mx, my = reaper.ImGui_GetMousePos(ctx)
  if marker_drag then
    local drag_btn = marker_drag.button or X.C_LEFT
    if marker_drag.id ~= a.id then
      marker_drag = nil
    elseif reaper.ImGui_IsMouseDown(ctx, drag_btn) then
      local marker = a.markers[marker_drag.idx]
      if marker then marker.t = math.max(0, math.min(L, xt(mx) + (marker_drag.offset or 0))) end
    else
      marker_drag = nil
      table.sort(a.markers, function(p, q) return (tonumber(p.t) or 0) < (tonumber(q.t) or 0) end)
      X.marker_sel[a.id] = nil
      X.refresh_item_markers(a)
      X.save()
      status = "Position des marqueurs enregistrée."
    end
  end
  if wf_drag then
    if reaper.ImGui_IsMouseDown(ctx, X.C_LEFT) then
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
      X.apply_cue_changes(a)
    else
      wf_drag = nil
      reaper.UpdateArrange()
      X.save()
    end
  end
  if cv_drag then
    if reaper.ImGui_IsMouseDown(ctx, X.C_LEFT) then
      local pt = env[cv_drag.idx]
      if pt then
        local lo = env[cv_drag.idx-1] and (env[cv_drag.idx-1].t + 0.001) or a.inpt
        local hi = env[cv_drag.idx+1] and (env[cv_drag.idx+1].t - 0.001) or a.outpt
        pt.t = math.max(lo, math.min(hi, xt(mx)))
        pt.g = X.frac_to_g(1 - (my - yb0)/hw)
        X.apply_cue_changes(a)
      end
    else
      cv_drag = nil
      reaper.UpdateArrange()
      X.save()
    end
  end

  if body_hover then
    local g = X.frac_to_g(1 - (my - yb0)/hw)
    reaper.ImGui_Text(ctx, string.format("t = %.3f s   gain = %s", xt(mx),
      g <= 0 and "-inf" or string.format("%.1f dB", 20*math.log(g,10))))
  end
  reaper.ImGui_TextDisabled(ctx, "Clic = tête de lecture  |  Alt+clic = courbe  |  Ctrl+clic = supprimer un point")
  if reaper.ImGui_SmallButton(ctx, "Réinitialiser la courbe##envreset") then a.env = {}; X.save() end

  reaper.ImGui_Separator(ctx)
  reaper.ImGui_Text(ctx, "Marqueurs de la source (temps en secondes)")

  local msel = X.marker_sel[a.id]
  if msel and not a.markers[msel] then msel = nil; X.marker_sel[a.id] = nil end
  local mtarget = msel
  if not mtarget then
    for k = #a.markers, 1, -1 do
      if tostring(a.markers[k].name or "") == "" then mtarget = k; break end
    end
  end
  if reaper.ImGui_Button(ctx, "Ajouter marqueur##mk_add") then
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
    local newm = {t = best_t, name = "", color = 0}
    a.markers[#a.markers + 1] = newm
    table.sort(a.markers, function(p, q) return (tonumber(p.t) or 0) < (tonumber(q.t) or 0) end)
    for k, m in ipairs(a.markers) do
      if m == newm then X.marker_sel[a.id] = k; X.marker_focus = {id = a.id, idx = k}; break end
    end
    X.save()
    status = string.format("Marqueur créé à %.3f s : saisis l'ID (ex. Q3) ou clique « Capturer cues ».", best_t)
  end
  reaper.ImGui_SameLine(ctx)
  local _, npicked = X.picked_any_names()
  local cap_label = string.format("Capturer cues (%d) → %s###mk_capture", npicked,
    mtarget and ("marqueur " .. mtarget) or "aucun marqueur")
  if reaper.ImGui_Button(ctx, cap_label) then
    local names, n = X.picked_any_names()
    if not mtarget then
      status = "Crée un marqueur (Ajouter marqueur) ou clique dans le champ du marqueur à renseigner."
    elseif n == 0 then
      status = "Aucune action sélectionnée : clique d'abord le TITRE d'une ligne dans la liste (Ctrl/Maj pour plusieurs)."
    else
      a.markers[mtarget].name = names
      X.marker_sel[a.id] = mtarget
      X.cap_n[a.id] = X.cap_n[a.id] + 1
      X.refresh_item_markers(a)
      X.save()
      status = n .. " action(s) capturée(s) dans le marqueur " .. mtarget .. " : " .. names
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Supprimer##mk_delete") then
    if msel then X.delete_marker = {id = a.id, idx = msel}
    else status = "Clique d'abord dans le champ du marqueur à supprimer." end
  end
  local sel_names = X.picked_any_names()
  reaper.ImGui_TextDisabled(ctx, "Sélection : " .. (sel_names ~= "" and sel_names or "(aucune)")
    .. "   |   Marqueur visé : " .. (mtarget and tostring(mtarget) or "—"))

  if #a.markers == 0 then
    reaper.ImGui_TextDisabled(ctx, "Aucun marqueur.")
  else
    local remove_marker, markers_changed = nil, false
    if X.delete_marker and X.delete_marker.id == a.id then
      remove_marker = X.delete_marker.idx
      X.delete_marker = nil
    end
    local shortcut_mod = reaper.ImGui_GetKeyMods and reaper.ImGui_Mod_Shortcut
      and (reaper.ImGui_GetKeyMods(ctx) & reaper.ImGui_Mod_Shortcut()) ~= 0
      or (reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_LeftCtrl()) or reaper.ImGui_IsKeyDown(ctx, reaper.ImGui_Key_RightCtrl()))
    for i, marker in ipairs(a.markers) do
      reaper.ImGui_PushID(ctx, 50000 + i)
      reaper.ImGui_Text(ctx, X.marker_sel[a.id] == i and "►" or " ")
      reaper.ImGui_SameLine(ctx)
      reaper.ImGui_SetNextItemWidth(ctx, X.S(80))
      local ct, mt = reaper.ImGui_InputDouble(ctx, "Temps##marktime", tonumber(marker.t) or 0, 0, 0, "%.3f")
      if ct then marker.t = math.max(0, math.min(L, mt)); markers_changed = true end
      reaper.ImGui_SameLine(ctx)
      reaper.ImGui_SetNextItemWidth(ctx, X.S(220))
      if X.marker_focus and X.marker_focus.id == a.id and X.marker_focus.idx == i then
        reaper.ImGui_SetKeyboardFocusHere(ctx)
        X.marker_focus = nil
      end
      local cn, mn = reaper.ImGui_InputText(ctx, "ID##markname" .. (X.cap_n[a.id] or 0), tostring(marker.name or ""))
      if cn then marker.name = mn; markers_changed = true end
      if reaper.ImGui_IsItemActive(ctx) or reaper.ImGui_IsItemClicked(ctx) then
        X.marker_sel[a.id] = i
        if shortcut_mod and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Delete(), false) then
          remove_marker = i
        end
      end
      reaper.ImGui_PopID(ctx)
    end
    if remove_marker and a.markers[remove_marker] then
      table.remove(a.markers, remove_marker)
      X.marker_sel[a.id] = nil
      markers_changed = true
      status = "Marqueur supprimé de la cue."
    end
    if markers_changed then
      local sorted = true
      for k = 2, #a.markers do
        if (tonumber(a.markers[k-1].t) or 0) > (tonumber(a.markers[k].t) or 0) then sorted = false; break end
      end
      if not sorted then
        local cur = X.marker_sel[a.id] and a.markers[X.marker_sel[a.id]] or nil
        table.sort(a.markers, function(p, q) return (tonumber(p.t) or 0) < (tonumber(q.t) or 0) end)
        if cur then for k, m in ipairs(a.markers) do if m == cur then X.marker_sel[a.id] = k; break end end end
      end
      X.refresh_item_markers(a)
      X.save()
    end
  end
  reaper.ImGui_TextDisabled(ctx, "Seuls les marqueurs situés entre IN et OUT seront copiés sur l'item.")
  X.draw_play_settings(a)
end

---------------------------------------------------------------- Éditeur d'action
-- Onglet "Snapshot lié" commun (cue, stop, pause, devamp).
function X.draw_linked_snapshot_tab(a, time_label)
  local c6, hp = reaper.ImGui_Checkbox(ctx, "Lier un état de pistes à cette action##hassnap", a.has_snapshot or false)
  if c6 then a.has_snapshot = hp; X.save() end
  if a.has_snapshot then
    -- Projet source du preset lié (indépendant de a.projfn, qui pour un CUE
    -- désigne la région source). Permet de cibler un autre onglet projet.
    local lib = X.find_project(a.snap_projfn)
    local none = (not a.snap_projfn or a.snap_projfn == "")
    local plabel = none and X.project_label(PROJ)
      or ((a.snap_projfn:match("([^/\\]+)$") or a.snap_projfn)..(lib and "" or " (non ouvert)"))
    if reaper.ImGui_BeginCombo(ctx, "Projet source du snapshot##linked_projsrc", plabel) then
      if reaper.ImGui_Selectable(ctx, X.project_label(PROJ).."##lproj0", none) then
        a.snap_projfn = nil; X.save()
      end
      for k, o in ipairs(X.other_projects()) do
        if o.fn ~= "" and reaper.ImGui_Selectable(ctx, o.label.."##lproj"..k, a.snap_projfn == o.fn) then
          a.snap_projfn = o.fn; X.save()
        end
      end
      reaper.ImGui_EndCombo(ctx)
    end
    X.draw_snap_editor(a, lib or PROJ)
    if time_label then
      local c7, lt = reaper.ImGui_Checkbox(ctx, time_label .. "##linktime", a.link_time or false)
      if c7 then a.link_time = lt; X.save() end
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
      X.save()
    else
      a.targets_text_error = "Format invalide : utilise Q1,Q8 (IDs numériques séparés par des virgules)."
    end
  end
  if a.targets_text_error then reaper.ImGui_TextColored(ctx, 0xFF4033FF, a.targets_text_error) end
  if kind == "pause" then
    local blocked = {}
    for _, tid in ipairs(a.targets or {}) do
      for _, tab in ipairs(tabs or {}) do
        for _, source_cue in ipairs(tab.actions or {}) do
          if tostring(source_cue.id) == tostring(tid) and X.is_region_cue(source_cue) then
            blocked[#blocked+1] = "Q" .. tostring(tid)
          end
        end
      end
    end
    if #blocked > 0 then
      reaper.ImGui_TextColored(ctx, 0xF39C12FF, "Attention : les cibles REGION " .. table.concat(blocked, ", ") .. " ne seront pas mises en pause. Retire-les de la liste ; seules les cues AUDIO sont prises en charge.")
    else
      reaper.ImGui_TextDisabled(ctx, "PAUSE / UNPAUSE : seules les cues AUDIO sont prises en charge. Les régions seront ignorées.")
    end
  end

  if reaper.ImGui_Button(ctx, "Capturer les cues sélectionnées (tous onglets)" .. pre .. "capture") then
    local ids = {}
    for _, tab in ipairs(tabs or {}) do
      for _, x in ipairs(tab.actions or {}) do
        if picked[x.id] and X.is_playable_cue(x) and not (kind == "pause" and X.is_region_cue(x)) then ids[#ids+1] = x.id end
      end
    end
    if #ids == 0 then
      status = "Aucune cue sélectionnée dans les onglets."
    else
      a.targets = ids
      local parts = {}; for _, id in ipairs(ids) do parts[#parts+1] = "Q"..tostring(id) end
      a.targets_text = table.concat(parts, ",")
      a.targets_text_error = nil
      X.save(); status = #ids.." cue(s) ciblée(s)."
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "Toutes les cues" .. pre .. "all") then
    a.targets = nil; a.targets_text = ""; a.targets_text_error = nil; X.save()
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

  -- DEVAMP : la cible reste disponible pour les sources AUDIO comme REGION.
  -- Le crossfade est utilisé uniquement lorsqu'une REGION enchaîne vers une REGION.
  if kind == "devamp" then
    local has_region_source, has_audio_source = false, false
    if a.targets and #a.targets > 0 then
      for _, tid in ipairs(a.targets) do
        for _, tab in ipairs(tabs or {}) do
          for _, source_cue in ipairs(tab.actions or {}) do
            if tostring(source_cue.id) == tostring(tid) then
              if X.is_region_cue(source_cue) then has_region_source = true
              elseif X.is_file_cue(source_cue) then has_audio_source = true end
            end
          end
        end
      end
    else
      has_region_source = true -- cible « toutes les cues » : le moteur filtre selon le type réel
    end

    if has_region_source then
      reaper.ImGui_Separator(ctx)
      local cxf, xf = reaper.ImGui_InputDouble(ctx, "Crossfade entre régions (s)##devamp_crossfade", tonumber(a.devamp_crossfade) or 0)
      if cxf then a.devamp_crossfade = math.max(0, math.min(30, xf)); X.save() end
      reaper.ImGui_TextDisabled(ctx, "Utilisé seulement si la cible après Devamp est une REGION. 0 = sans crossfade.")
    end
    if has_audio_source then
      reaper.ImGui_TextDisabled(ctx, "Pour une source AUDIO, le Devamp sort sur sa propre boucle ; la cible démarre ensuite sans crossfade de région.")
    end

    -- Pour une source AUDIO seule, le Devamp termine sur sa propre boucle :
    -- masquer les réglages d'enchaînement pour éviter toute confusion.
    -- Si la source est une REGION (ou si toutes les cues sont ciblées), on garde
    -- la destination, qui peut être une REGION ou une cue AUDIO.
    local show_chain_after_devamp = not (has_audio_source and not has_region_source)
    if show_chain_after_devamp then
    reaper.ImGui_Separator(ctx)
    reaper.ImGui_Text(ctx, "Enchaîner après le Devamp (optionnel) :")
    reaper.ImGui_TextDisabled(ctx, "La cible peut être une cue AUDIO ou REGION. Le crossfade ne s'applique qu'à REGION → REGION.")
    local to_text = a.devamp_to_text
    if to_text == nil then
      to_text = a.devamp_to and ("Q"..tostring(a.devamp_to)) or ""
      a.devamp_to_text = to_text
    end
    local ct2, new_to = reaper.ImGui_InputText(ctx, "Cible après Devamp##devamp_to_text", to_text)
    if ct2 then
      a.devamp_to_text = new_to
      local digits = new_to:match("^%s*[Qq]?(%d+)%s*$")
      if new_to:match("^%s*$") then
        a.devamp_to = nil
        a.devamp_to_error = nil
        X.save()
      elseif digits then
        local candidate = tonumber(digits)
        local target_is_playable = false
        for _, tab in ipairs(tabs or {}) do
          for _, x in ipairs(tab.actions or {}) do
            if tonumber(x.id) == candidate and X.is_playable_cue(x) then target_is_playable = true end
          end
        end
        if target_is_playable then
          a.devamp_to = candidate
          a.devamp_to_error = nil
          X.save()
        else
          a.devamp_to_error = "La cible doit être une cue AUDIO ou REGION (ex. Q12)."
        end
      else
        a.devamp_to_error = "Format : Q12 (un seul ID de cue AUDIO ou REGION)."
      end
    end
    if a.devamp_to_error then
      reaper.ImGui_TextColored(ctx, 0xFF4033FF, a.devamp_to_error)
    end
    if reaper.ImGui_Button(ctx, "Capturer la sélection comme cible après Devamp##devamp_to_cap") then
      local one
      for _, tab in ipairs(tabs or {}) do
        for _, x in ipairs(tab.actions or {}) do
          if picked[x.id] and X.is_playable_cue(x) then
            if one and one ~= x.id then one = false; break end
            one = x.id
          end
        end
        if one == false then break end
      end
      if one and one ~= false then
        a.devamp_to = one
        a.devamp_to_text = "Q"..tostring(one)
        a.devamp_to_error = nil
        X.save()
        status = "Devamp enchaînera vers Q"..tostring(one).."."
      else
        status = "Sélectionnez exactement une cue AUDIO ou REGION comme cible après Devamp."
      end
    end
    if a.devamp_to then
      local nmx, tabname = "(introuvable)", "?"
      for _, tab in ipairs(tabs or {}) do
        for _, x in ipairs(tab.actions or {}) do
          if tostring(x.id) == tostring(a.devamp_to) then
            nmx, tabname = (x.name or "?"), (tab.name or "?")
            break
          end
        end
      end
      reaper.ImGui_BulletText(ctx, string.format("Après Devamp → Q%s — %s (%s)", tostring(a.devamp_to), nmx, tabname))
    end
    end -- show_chain_after_devamp
  end -- options de destination Devamp
end

function X.draw_editor(a, i)
  reaper.ImGui_Separator(ctx)
  local ch, v = reaper.ImGui_InputText(ctx, "Nom", a.name)
  if ch then
    a.name = v
    -- STOP / PAUSE / DEVAMP : nommer manuellement fige le titre affiché
    -- (sinon il reste calculé à partir des cues ciblées).
    if a.type == "stop" or a.type == "pause" or a.type == "devamp" then
      a.custom_title = true
    end
    X.save()
  end
  if (a.type == "stop" or a.type == "pause" or a.type == "devamp") and a.custom_title then
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_SmallButton(ctx, "Titre auto##reset_title") then
      a.custom_title = nil
      X.save()
      status = "Titre automatique restauré."
    end
  end

  if a.type == "audio" then
    -- AUDIO fichier uniquement.
    a.type = "audio"
    a.src = "file"
    if reaper.ImGui_BeginTabBar(ctx, "cuetabs") then
      if reaper.ImGui_BeginTabItem(ctx, "Source") then
        reaper.ImGui_Text(ctx, (a.file and a.file ~= "") and a.file or "(aucun fichier)")
        if reaper.ImGui_Button(ctx, "Choisir un fichier...") then
          local ok, f = reaper.GetUserFileNameForRead(a.file or "", "Fichier audio", "")
          if ok and f ~= "" then X.assign_audio_file(a, f) end
        end
        reaper.ImGui_SameLine(ctx)
        if reaper.ImGui_Button(ctx, "Supprimer fichier##source_clear") then
          a.file, a.inpt, a.outpt, a.env = nil, nil, nil, nil
          a.markers, a.marker_name = {}, "Q1"
          a.view_zoom, a.view_offset = 1.0, 0.0
          X.save()
        end

        local c, g = X.track_combo("Piste cible", a.track, false)
        if c then a.track = g; X.save() end

        local c4, fi = reaper.ImGui_InputDouble(ctx, "Fade in (s)", a.fadein or 0)
        if c4 then a.fadein = math.max(0, fi); X.save() end
        reaper.ImGui_SetNextItemWidth(ctx, X.S(220))
        local cfc, fc = reaper.ImGui_SliderDouble(ctx, "Courbe du fade##cue_curve", tonumber(a.fade_curve) or 0, 0, 1, "Léger  %.2f  Prononcé")
        if cfc then a.fade_curve = math.max(0, math.min(1, fc)); X.save() end
        reaper.ImGui_TextDisabled(ctx, "0 = linéaire ; augmentez le curseur pour accentuer la courbe des fades de cette cue.")

        reaper.ImGui_Separator(ctx)
        local ca, auto_value = reaper.ImGui_Checkbox(ctx, "AUTO : délai depuis le déclenchement", a.auto == true)
        if ca then a.auto = auto_value; if auto_value then a.follow = false end; X.save() end
        local cf, follow_value = reaper.ImGui_Checkbox(ctx, "FOLLOW : attendre la fin puis le délai", a.follow == true)
        if cf then a.follow = follow_value; if follow_value then a.auto = false end; X.save() end
        reaper.ImGui_SetNextItemWidth(ctx, X.S(110))
        local cd, delay_value = reaper.ImGui_InputDouble(ctx, "DELAY (s)##auto_delay", tonumber(a.delay) or 0, 0, 0, "%.2f")
        if cd then a.delay = math.max(0, delay_value); X.save() end
        reaper.ImGui_TextDisabled(ctx, "AUTO et FOLLOW sont exclusifs. DELAY s'applique au mode choisi.")

        reaper.ImGui_EndTabItem(ctx)
      end

      if reaper.ImGui_BeginTabItem(ctx, "Forme d'onde") then
        X.draw_wave_editor(a)
        reaper.ImGui_EndTabItem(ctx)
      end

      if reaper.ImGui_BeginTabItem(ctx, "Snapshot lié") then
        X.draw_linked_snapshot_tab(a, "Lier le temps du snapshot au fade in")
        reaper.ImGui_EndTabItem(ctx)
      end
      reaper.ImGui_EndTabBar(ctx)
    end

  elseif a.type == "region" then
    -- CUE région (projet / région / copie ou in-place).
    a.src = "region"
    if reaper.ImGui_BeginTabBar(ctx, "regiontabs") then
      if reaper.ImGui_BeginTabItem(ctx, "Source") then
        local lib = X.find_project(a.projfn)
        local none = (not a.projfn or a.projfn == "")
        local plabel = none and X.project_label(PROJ) or ((a.projfn:match("([^/\\]+)$") or a.projfn)..(lib and "" or " (non ouvert)"))
        if reaper.ImGui_BeginCombo(ctx, "Projet source##projsrc", plabel) then
          if reaper.ImGui_Selectable(ctx, X.project_label(PROJ).."##proj0", none) then
            a.projfn, a.region = nil, nil; X.save()
          end
          for k, o in ipairs(X.other_projects()) do
            if o.fn ~= "" and reaper.ImGui_Selectable(ctx, o.label.."##proj"..k, a.projfn == o.fn) then
              a.projfn, a.region = o.fn, nil; X.save()
            end
          end
          reaper.ImGui_EndCombo(ctx)
        end
        local regs = lib and X.get_regions(lib) or {}
        local preview = "(choisir)"
        for _, r in ipairs(regs) do if r.idx == a.region then preview = r.name end end
        if reaper.ImGui_BeginCombo(ctx, "Région##regcombo", preview) then
          for _, r in ipairs(regs) do
            if reaper.ImGui_Selectable(ctx, r.name.."##r"..r.idx, r.idx == a.region) then
              a.region = r.idx; X.save()
            end
          end
          reaper.ImGui_EndCombo(ctx)
        end

        local inplace = a.projfn and a.projfn ~= "" and not a.copy
        if a.projfn and a.projfn ~= "" then
          local cc, cv = reaper.ImGui_Checkbox(ctx, "Copier les items dans ce projet##copy", a.copy or false)
          if cc then a.copy = cv; X.save() end
        end

        local c, g = false, a.track
        if inplace then
          reaper.ImGui_TextDisabled(ctx, "La région joue dans son propre onglet (transport + FX du projet source).")
        else
          c, g = X.track_combo("Piste cible", a.track, true)
        end
        if c then a.track = g; X.save() end

        local c4, fi = reaper.ImGui_InputDouble(ctx, "Fade in (s)", a.fadein or 0)
        if c4 then a.fadein = math.max(0, fi); X.save() end
        reaper.ImGui_SetNextItemWidth(ctx, X.S(220))
        local cfc, fc = reaper.ImGui_SliderDouble(ctx, "Courbe du fade##reg_curve", tonumber(a.fade_curve) or 0, 0, 1, "Léger  %.2f  Prononcé")
        if cfc then a.fade_curve = math.max(0, math.min(1, fc)); X.save() end
        reaper.ImGui_TextDisabled(ctx, "0 = linéaire ; augmentez le curseur pour accentuer la courbe des fades de cette cue.")

        reaper.ImGui_Separator(ctx)
        local cloop, loopv = reaper.ImGui_Checkbox(ctx, "Boucle (région entière)##reg_loop", a.loop == true)
        if cloop then a.loop = loopv; X.save() end
        if a.loop then
          reaper.ImGui_SameLine(ctx)
          reaper.ImGui_Text(ctx, "Cycles :")
          reaper.ImGui_SameLine(ctx)
          if reaper.ImGui_SmallButton(ctx, "−##reg_cycle_minus") then
            local n = tonumber(a.loop_count) or 0
            a.loop_count = (n > 1) and (n - 1) or nil -- vide/0 = infini
            X.save()
          end
          reaper.ImGui_SameLine(ctx)
          reaper.ImGui_Text(ctx, (tonumber(a.loop_count) and tonumber(a.loop_count) > 0) and tostring(a.loop_count) or "∞")
          reaper.ImGui_SameLine(ctx)
          if reaper.ImGui_SmallButton(ctx, "+##reg_cycle_plus") then
            a.loop_count = math.max(1, tonumber(a.loop_count) or 0) + ((tonumber(a.loop_count) or 0) > 0 and 1 or 0)
            X.save()
          end
        end
        reaper.ImGui_TextDisabled(ctx, "Boucle : revient au début de la région à la fin. DEVAMP = terminer le cycle en cours puis s'arrêter.")

        reaper.ImGui_Separator(ctx)
        local ca, auto_value = reaper.ImGui_Checkbox(ctx, "AUTO : délai depuis le déclenchement", a.auto == true)
        if ca then a.auto = auto_value; if auto_value then a.follow = false end; X.save() end
        local cf, follow_value = reaper.ImGui_Checkbox(ctx, "FOLLOW : attendre la fin puis le délai", a.follow == true)
        if cf then a.follow = follow_value; if follow_value then a.auto = false end; X.save() end
        reaper.ImGui_SetNextItemWidth(ctx, X.S(110))
        local cd, delay_value = reaper.ImGui_InputDouble(ctx, "DELAY (s)##reg_delay", tonumber(a.delay) or 0, 0, 0, "%.2f")
        if cd then a.delay = math.max(0, delay_value); X.save() end
        reaper.ImGui_TextDisabled(ctx, "AUTO et FOLLOW sont exclusifs. DELAY s'applique au mode choisi.")

        reaper.ImGui_EndTabItem(ctx)
      end

      if reaper.ImGui_BeginTabItem(ctx, "Snapshot lié") then
        X.draw_linked_snapshot_tab(a, "Lier le temps du snapshot au fade in")
        reaper.ImGui_EndTabItem(ctx)
      end
      reaper.ImGui_EndTabBar(ctx)
    end

  elseif a.type == "stop" or a.type == "pause" or a.type == "devamp" then
    if reaper.ImGui_BeginTabBar(ctx, "acttabs_" .. a.type) then
      if reaper.ImGui_BeginTabItem(ctx, "Réglages") then
        if a.type == "stop" then
          local c2, d = reaper.ImGui_InputDouble(ctx, "Durée du fade (s)", a.dur or 0)
          if c2 then a.dur = math.max(0, d); X.save() end
          reaper.ImGui_TextDisabled(ctx, "0 = arrêt immédiat (affiché STOP) ; > 0 = FADEOUT.")
        elseif a.type == "pause" then
          local cu, un = reaper.ImGui_Checkbox(ctx, "Unpause (reprendre les cues en pause)##unpause", a.unpause == true)
          if cu then a.unpause = un; X.save() end
          local lbl = a.unpause == true and "Fade in après unpause (s)" or "Fade out avant pause (s)"
          local c2, d = reaper.ImGui_InputDouble(ctx, lbl .. "##pausedur", a.dur or 0)
          if c2 then a.dur = math.max(0, d); X.save() end
          if a.unpause ~= true and (a.dur or 0) > PAUSE_FADE_MAX then
            reaper.ImGui_TextColored(ctx, 0xF39C12FF, string.format("Fade out limité à %.0f s (planification à l'avance).", PAUSE_FADE_MAX))
          end
        else
          reaper.ImGui_TextDisabled(ctx, "Arme le Devamp sur les cues ciblées : elles finissent leur passage jusqu'à Lo puis filent vers OUT.")
        end
        X.draw_targets_editor(a, a.type)
        reaper.ImGui_EndTabItem(ctx)
      end
      if reaper.ImGui_BeginTabItem(ctx, "Snapshot lié") then
        X.draw_linked_snapshot_tab(a, a.type == "stop" and "Lier le temps du snapshot à la durée du fade"
          or (a.type == "pause" and "Lier le temps du snapshot au fade" or nil))
        reaper.ImGui_EndTabItem(ctx)
      end
      reaper.ImGui_EndTabBar(ctx)
    end

  elseif a.type == "osc" then
    local preview = (a.port_name and a.port_name ~= "") and a.port_name or "(choisir un port)"
    if reaper.ImGui_BeginCombo(ctx, "Port OSC##oscport", preview) then
      for _, p in ipairs(prefs.ports or {}) do
        if reaper.ImGui_Selectable(ctx, p.name.."##p"..p.name, a.port_name == p.name) then
          a.port_name = p.name; X.save()
        end
      end
      reaper.ImGui_EndCombo(ctx)
    end
    local c, addr = reaper.ImGui_InputText(ctx, "Adresse##oscaddr", a.address or "/")
    if c then a.address = addr; X.save() end
    reaper.ImGui_TextDisabled(ctx, "Arguments (séparés par des espaces) :")
    local argstr = table.concat(a.args or {}, " ")
    local c2, newargs = reaper.ImGui_InputText(ctx, "##oscargs", argstr)
    if c2 then
      a.args = {}
      for token in newargs:gmatch("%S+") do
        local n = tonumber(token)
        a.args[#a.args+1] = n or token
      end
      X.save()
    end
    if not has_socket then
      reaper.ImGui_TextColored(ctx, 0xF39C12FF, "LuaSocket manquant → l'envoi OSC est désactivé.")
    end

  elseif a.type == "midi" then
    local c, g = X.track_combo("Piste cible##miditr", a.track, false)
    if c then a.track = g; X.save() end
    local types = {"note", "cc", "pc"}
    local labels = {note="Note", cc="Control Change", pc="Program Change"}
    if reaper.ImGui_BeginCombo(ctx, "Type##miditype", labels[a.midi_type or "note"]) then
      for _, t in ipairs(types) do
        if reaper.ImGui_Selectable(ctx, labels[t].."##mt"..t, a.midi_type == t) then
          a.midi_type = t; X.save()
        end
      end
      reaper.ImGui_EndCombo(ctx)
    end
    local cch, chv = reaper.ImGui_InputInt(ctx, "Canal (1-16)##midich", a.channel or 1)
    if cch then a.channel = math.max(1, math.min(16, chv)); X.save() end
    if a.midi_type == "note" then
      local cn, nv = reaper.ImGui_InputInt(ctx, "Note (0-127)##midinote", a.note or 60)
      if cn then a.note = math.max(0, math.min(127, nv)); X.save() end
      local cv, vv = reaper.ImGui_InputInt(ctx, "Velocity##midivel", a.velocity or 100)
      if cv then a.velocity = math.max(0, math.min(127, vv)); X.save() end
    elseif a.midi_type == "cc" then
      local cc, cv = reaper.ImGui_InputInt(ctx, "CC (0-127)##midicc", a.cc or 1)
      if cc then a.cc = math.max(0, math.min(127, cv)); X.save() end
      local cv2, vv = reaper.ImGui_InputInt(ctx, "Valeur##midival", a.value or 0)
      if cv2 then a.value = math.max(0, math.min(127, vv)); X.save() end
    else
      local cp, pv = reaper.ImGui_InputInt(ctx, "Program (0-127)##midiprog", a.program or 0)
      if cp then a.program = math.max(0, math.min(127, pv)); X.save() end
    end

  else -- snapshot
    -- Projet source : comme pour les CUE, permet de cibler un autre onglet.
    local lib = X.find_project(a.projfn)
    local none = (not a.projfn or a.projfn == "")
    local plabel = none and X.project_label(PROJ)
      or ((a.projfn:match("([^/\\]+)$") or a.projfn)..(lib and "" or " (non ouvert)"))
    if reaper.ImGui_BeginCombo(ctx, "Projet source##snap_projsrc", plabel) then
      if reaper.ImGui_Selectable(ctx, X.project_label(PROJ).."##pproj0", none) then
        a.projfn = nil; X.save()
      end
      for k, o in ipairs(X.other_projects()) do
        if o.fn ~= "" and reaper.ImGui_Selectable(ctx, o.label.."##pproj"..k, a.projfn == o.fn) then
          a.projfn = o.fn; X.save()
        end
      end
      reaper.ImGui_EndCombo(ctx)
    end
    local c2, d = reaper.ImGui_InputDouble(ctx, "Transition (s)", a.dur or 0)
    if c2 then a.dur = math.max(0, d); X.save() end
    X.draw_snap_editor(a, X.find_project(a.projfn) or PROJ)
  end

  reaper.ImGui_Spacing(ctx)
  reaper.ImGui_TextDisabled(ctx, "Supprimer : Ctrl/Cmd + clic sur le N° de la ligne.")
end

---------------------------------------------------------------- Préférences
function X.draw_prefs()
  if reaper.ImGui_CollapsingHeader(ctx, "Préférences générales") then
    local c1, v1 = reaper.ImGui_Checkbox(ctx, "Arrêter la lecture quand plus aucun média n'est joué", prefs.auto_stop == true)
    if c1 then
      prefs.auto_stop = v1 and true or false
      cue_session, idle_since = false, nil
      X.save()
      status = prefs.auto_stop and "Auto-stop transport : ACTIVÉ" or "Auto-stop transport : DÉSACTIVÉ"
    end
    local c2, v2 = reaper.ImGui_Checkbox(ctx, "Delete on stop", prefs.delete_on_stop == true)
    if c2 then
      prefs.delete_on_stop = v2 and true or false
      if not prefs.delete_on_stop then
        -- Annuler les suppressions différées en attente.
        del_jobs = {}
      end
      X.save()
    end
    reaper.ImGui_SetNextItemWidth(ctx, X.S(220))
    local ccurve, curve = reaper.ImGui_SliderDouble(ctx, "Courbe du STOP global##stop_curve", stop_curve, 0, 1, "Logarithmique  %.2f  Exponentiel")
    if ccurve then
      stop_curve = math.max(0, math.min(1, curve))
      reaper.SetExtState(EXT, "stopcurve", tostring(stop_curve), true)
    end
    reaper.ImGui_TextDisabled(ctx, "À gauche : baisse rapide du niveau. Au centre : linéaire. À droite : niveau maintenu puis chute en fin de fade. La durée reste inchangée.")
    local c8, v8 = reaper.ImGui_Checkbox(ctx, "Une nouvelle cue remplace celle qui joue déjà sur la même piste", prefs.exclusive_track ~= false)
    if c8 then prefs.exclusive_track = v8; X.save() end

    reaper.ImGui_SetNextItemWidth(ctx, X.S(110))
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
      reaper.ImGui_SameLine(ctx, X.S(80))
      reaper.ImGui_SetNextItemWidth(ctx, X.S(180))
      local cn, nn = reaper.ImGui_InputText(ctx, "##name", p.name or "")
      if cn then p.name = nn; X.save() end
      reaper.ImGui_Text(ctx, "IP")
      reaper.ImGui_SameLine(ctx, X.S(80))
      reaper.ImGui_SetNextItemWidth(ctx, X.S(180))
      local ci, ni = reaper.ImGui_InputText(ctx, "##ip", p.ip or "127.0.0.1")
      if ci then p.ip = ni; X.save() end
      reaper.ImGui_Text(ctx, "Port")
      reaper.ImGui_SameLine(ctx, X.S(80))
      reaper.ImGui_SetNextItemWidth(ctx, X.S(100))
      local cp, np = reaper.ImGui_InputInt(ctx, "##port", p.port or 8000, 0, 0)
      if cp then p.port = math.max(1, math.min(65535, np)); X.save() end
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
      X.save()
    end
    if reaper.ImGui_Button(ctx, "+ Ajouter un port OSC") then
      prefs.ports[#prefs.ports+1] = {
        name = "Port " .. (#prefs.ports + 1),
        ip = "127.0.0.1",
        port = 8000
      }
      X.save()
    end
    if not has_socket then
      reaper.ImGui_TextColored(ctx, 0xF39C12FF, "Mavriq Lua Sockets 1.2 non détecté → l'envoi OSC est désactivé.")
      reaper.ImGui_TextDisabled(ctx, "Vérifie dans ReaPack que Mavriq Lua Sockets est installé en version 1.2.")
    end
    reaper.ImGui_Separator(ctx)
    reaper.ImGui_Text(ctx, "Apparence de l’interface")
    reaper.ImGui_SameLine(ctx)
    -- Petit carré discret dans les préférences générales : ouvre tous les réglages d’apparence.
    local swatch = X.interface_bg_color() or tonumber(prefs.bg_hue) or 0x3B82F6FF
    if reaper.ImGui_ColorButton then
      if reaper.ImGui_ColorButton(ctx, "##interface_appearance_prefs", swatch, 0, X.S(16), X.S(16)) then
        reaper.ImGui_OpenPopup(ctx, "Apparence de l’interface##appearance_popup")
      end
    elseif reaper.ImGui_Button(ctx, "■##interface_appearance_prefs", X.S(16), X.S(16)) then
      reaper.ImGui_OpenPopup(ctx, "Apparence de l’interface##appearance_popup")
    end
    if reaper.ImGui_IsItemHovered and reaper.ImGui_IsItemHovered(ctx) and reaper.ImGui_SetTooltip then
      reaper.ImGui_SetTooltip(ctx, "Réglages de couleur, de fond et de zoom")
    end
    if reaper.ImGui_BeginPopup(ctx, "Apparence de l’interface##appearance_popup") then
      reaper.ImGui_Text(ctx, "Apparence de l’interface")
      reaper.ImGui_Separator(ctx)
      if reaper.ImGui_ColorPicker3 then
        local flags = 0
        if reaper.ImGui_ColorPickerFlags_PickerHueWheel then flags = flags | reaper.ImGui_ColorPickerFlags_PickerHueWheel() end
        if reaper.ImGui_ColorPickerFlags_NoInputs then flags = flags | reaper.ImGui_ColorPickerFlags_NoInputs() end
        local changed, color = reaper.ImGui_ColorPicker3(ctx, "##bg_color_wheel", tonumber(prefs.bg_hue) or 0x3B82F6FF, flags)
        if changed then prefs.bg_hue = color; X.save() end
      elseif reaper.ImGui_ColorEdit3 then
        local changed, color = reaper.ImGui_ColorEdit3(ctx, "##bg_color_wheel", tonumber(prefs.bg_hue) or 0x3B82F6FF, 0)
        if changed then prefs.bg_hue = color; X.save() end
      end
      reaper.ImGui_SetNextItemWidth(ctx, X.S(230))
      local cbg, bgv = reaper.ImGui_SliderDouble(ctx, "Fond : noir → blanc##bg_level", tonumber(prefs.bg_level) or 0, 0, 1, "%.2f")
      if cbg then prefs.bg_level = bgv; X.save() end
      reaper.ImGui_SetNextItemWidth(ctx, X.S(230))
      local csat, sat = reaper.ImGui_SliderDouble(ctx, "Saturation##bg_saturation", tonumber(prefs.bg_saturation) or 0, 0, 1, "%.2f")
      if csat then prefs.bg_saturation = sat; X.save() end
      reaper.ImGui_Separator(ctx)
      reaper.ImGui_SetNextItemWidth(ctx, X.S(230))
      local cz, zv = reaper.ImGui_SliderDouble(ctx, "Zoom interface##zoom", ui_scale, 0.6, 2.5, "%.2f×")
      if cz then X.set_zoom(zv) end
      reaper.ImGui_SameLine(ctx)
      if reaper.ImGui_SmallButton(ctx, "100%##zoomreset_popup") then X.set_zoom(1.0) end
      reaper.ImGui_EndPopup(ctx)
    end

    -- Carré voisin : couleur des éléments bleus (boutons, onglets et contrôles actifs).
    reaper.ImGui_SameLine(ctx)
    local accent_swatch = X.accent_color()
    if reaper.ImGui_ColorButton then
      if reaper.ImGui_ColorButton(ctx, "##interface_accent_prefs", accent_swatch, 0, X.S(16), X.S(16)) then
        reaper.ImGui_OpenPopup(ctx, "Couleur des objets bleus##accent_popup")
      end
    elseif reaper.ImGui_Button(ctx, "■##interface_accent_prefs", X.S(16), X.S(16)) then
      reaper.ImGui_OpenPopup(ctx, "Couleur des objets bleus##accent_popup")
    end
    if reaper.ImGui_IsItemHovered and reaper.ImGui_IsItemHovered(ctx) and reaper.ImGui_SetTooltip then
      reaper.ImGui_SetTooltip(ctx, "Couleur des objets bleus de l’interface")
    end
    if reaper.ImGui_BeginPopup(ctx, "Couleur des objets bleus##accent_popup") then
      reaper.ImGui_Text(ctx, "Couleur des objets bleus")
      reaper.ImGui_Separator(ctx)
      if reaper.ImGui_ColorPicker3 then
        local flags = 0
        if reaper.ImGui_ColorPickerFlags_PickerHueWheel then flags = flags | reaper.ImGui_ColorPickerFlags_PickerHueWheel() end
        if reaper.ImGui_ColorPickerFlags_NoInputs then flags = flags | reaper.ImGui_ColorPickerFlags_NoInputs() end
        local changed, color = reaper.ImGui_ColorPicker3(ctx, "##accent_color_wheel", tonumber(prefs.accent_hue) or 0x3B82F6FF, flags)
        if changed then prefs.accent_hue = color; X.save() end
      elseif reaper.ImGui_ColorEdit3 then
        local changed, color = reaper.ImGui_ColorEdit3(ctx, "##accent_color_wheel", tonumber(prefs.accent_hue) or 0x3B82F6FF, 0)
        if changed then prefs.accent_hue = color; X.save() end
      end
      reaper.ImGui_SetNextItemWidth(ctx, X.S(230))
      local csat, sat = reaper.ImGui_SliderDouble(ctx, "Saturation##accent_saturation", tonumber(prefs.accent_saturation) or 1, 0, 1, "%.2f")
      if csat then prefs.accent_saturation = sat; X.save() end
      reaper.ImGui_EndPopup(ctx)
    end
  end
end

---------------------------------------------------------------- Draw principal
function X.draw()
  if tabs and tabs[active_tab] and actions and tabs[active_tab].actions ~= actions then
    tabs[active_tab].actions = actions -- filet de sécurité : jamais de liste d'onglet périmée
  end
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
      X.copy_picked_actions(false)
    elseif shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_X(), false) then
      X.copy_picked_actions(true)
    elseif shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_V(), false) then
      X.paste_picked_actions()
    elseif shortcut_down and (reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Delete(), false)
        or reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Backspace(), false)) then
      X.delete_picked()
    elseif shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Z(), false) then
      X.undo_change()
    elseif shortcut_down and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Y(), false) then
      X.redo_change()
    elseif reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Escape(), false) then
      auto_chain = nil
      X.fire_stop({dur = stop_fade})
    elseif selected and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Space(), false) then
      X.go_selected()
    end
  end

  local mx, my = reaper.ImGui_GetMousePos(ctx)
  local over_wave = false
  if wave_rect_x1 then
    if mx >= wave_rect_x1 and mx <= wave_rect_x2 and my >= wave_rect_y1 and my <= wave_rect_y2 then
      over_wave = true
    end
  end

  local _, ctrl = X.mods_shift_multi()
  if ctrl and not over_wave and reaper.ImGui_IsWindowHovered(ctx, reaper.ImGui_HoveredFlags_ChildWindows()) then
    local wheel = reaper.ImGui_GetMouseWheel(ctx)
    if wheel ~= 0 then X.set_zoom(ui_scale * (1 + 0.1 * wheel)) end
  end

  -- Barre d'onglets : les carrés sont réordonnables par glisser-déposer.
  for i, tab in ipairs(tabs) do
    if i > 1 then reaper.ImGui_SameLine(ctx) end
    local label = (i == active_tab and "[ " or "") .. (tab.name or ("Liste "..i)) .. (i == active_tab and " ]" or "") .. "##cue_list_tab_"..i
    if reaper.ImGui_Button(ctx, label) and i ~= active_tab then
      if tabs[active_tab] then tabs[active_tab].actions = actions end
      active_tab = i; X.sync_active_tab()
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
          X.sync_active_tab(); X.save(); status = "Onglets réorganisés."
        end
      end
      reaper.ImGui_EndDragDropTarget(ctx)
    end
  end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+##new_cue_list_tab") then
    tabs[#tabs+1] = {name = X.new_tab_name(), actions = {}}
    active_tab = #tabs; X.sync_active_tab()
    pick_anchor = nil
    X.save(); status = "Nouvel onglet créé."
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
      X.sync_active_tab()
      picked, pick_anchor, selected = {}, nil, nil
      X.save()
      status = "Liste active vidée. Les autres onglets sont conservés."
    end
  end
  if tab_name_edit then
    reaper.ImGui_SameLine(ctx)
    reaper.ImGui_SetNextItemWidth(ctx, X.S(130))
    local changed, value = reaper.ImGui_InputText(ctx, "Nom##cue_list_tab_name", tab_name_buffer)
    if changed then tab_name_buffer = value end
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_Button(ctx, "OK##cue_list_tab_name") then
      local name = (tab_name_buffer or ""):match("^%s*(.-)%s*$")
      if name ~= "" then tabs[tab_name_edit].name = name; X.save(); status = "Onglet renommé." end
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
      X.sync_active_tab(); picked, pick_anchor, selected = {}, nil, nil
      X.save(); status = "Onglet supprimé."
    end
    reaper.ImGui_SameLine(ctx)
    if reaper.ImGui_Button(ctx, "Non##cancel_delete_tab") then pending_delete_tab = nil end
  end
  reaper.ImGui_Separator(ctx)

  local sel_name = "-"
  for _, a in ipairs(actions) do if a.id == selected then sel_name = a.name end end

  local GREEN_GO = 0x2E8B57FF
  local WHITE_GO = 0xFFFFFFFF
  -- Contour gris, de l'épaisseur des lignes de l'interface (2 px).
  reaper.ImGui_PushStyleVar(ctx, reaper.ImGui_StyleVar_FrameBorderSize(), X.S(2))
  reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Border(), 0x8C8C8CFF)
  reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Button(), GREEN_GO)
  if reaper.ImGui_Col_ButtonHovered then reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_ButtonHovered(), GREEN_GO) end
  if reaper.ImGui_Col_ButtonActive then reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_ButtonActive(), GREEN_GO) end

  local go_pressed = false
  local go_w, go_h = X.S(110), X.S(80)
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
      local go_font_size = math.max(X.S(54), 60 * ui_scale)
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
      local thick = math.max(4, X.S(5))
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
      local base_size = reaper.ImGui_GetFontSize and reaper.ImGui_GetFontSize(ctx) or X.S(13)
      local ok = pcall(reaper.ImGui_PushFont, ctx, nil, math.max(X.S(54), 60 * ui_scale))
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

  local go_pop_count = 2 -- Border + Button
  if reaper.ImGui_Col_ButtonHovered then go_pop_count = go_pop_count + 1 end
  if reaper.ImGui_Col_ButtonActive then go_pop_count = go_pop_count + 1 end
  reaper.ImGui_PopStyleColor(ctx, go_pop_count)
  reaper.ImGui_PopStyleVar(ctx, 1)
  if go_pressed then X.go_selected() end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_Text(ctx, "Prochaine : "..sel_name)

  if reaper.ImGui_Button(ctx, "+ Audio") then X.add_action("audio") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Region") then X.add_action("region") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Snapshot") then X.add_action("snapshot") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Stop") then X.add_action("stop") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Pause") then X.add_action("pause") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ Devamp") then X.add_action("devamp") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ OSC") then X.add_action("osc") end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "+ MIDI") then X.add_action("midi") end

  if reaper.ImGui_Button(ctx, "New") then
    if reaper.MB("Créer une nouvelle session ?\nToutes les listes et tous leurs onglets seront vidés.", "ActionList — Nouvelle session", 4) == 6 then
      for _, tab in ipairs(tabs) do tab.actions = {} end
      X.sync_active_tab()
      picked, pick_anchor, selected = {}, nil, nil
      cue_clipboard, clipboard_cut = nil, false
      X.save()
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
              active_tab = d.active_tab or 1
              if type(d.actions) == "table" and tabs[active_tab] then tabs[active_tab].actions = d.actions end
              X.sync_active_tab()
            else
              actions = d.actions or {}; tabs = {{name = "Liste 1", actions = actions}}; active_tab = 1; X.sync_active_tab()
            end
            if type(d.prefs) == "table" then
              for k, pv in pairs(d.prefs) do prefs[k] = pv end
            end
            if not prefs.ports then prefs.ports = {} end
            picked, pick_anchor, selected = {}, nil, nil
            local missing_media = X.resolve_loaded_media_paths(f)
            X.save()
            if not missing_media or missing_media == 0 then status = "ActionList chargée : "..f end
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
    -- Le sélecteur natif permet de choisir le nom du fichier Lua, mais ne permet
    -- pas d'ajouter une case personnalisée à sa fenêtre. La case Bundle reste
    -- à côté de Save et détermine le mode utilisé après le choix du nom.
    local f = nil
    if reaper.JS_Dialog_BrowseForSaveFile then
      local ok, filename = reaper.JS_Dialog_BrowseForSaveFile(
        prefs.save_bundle == true and "Enregistrer le Bundle ReaLive (nom du fichier Lua)" or "Enregistrer l'ActionList",
        "", "ActionList.lua", "*.lua")
      if ok and filename and filename ~= "" then f = filename end
    else
      local ok, filename = reaper.GetUserFileNameForRead(
        "", prefs.save_bundle == true and "Enregistrer le Bundle ReaLive (taper le nom du fichier Lua)" or "Enregistrer l'ActionList (taper le nom et valider)", "*.lua")
      if ok and filename and filename ~= "" then f = filename end
    end
    if f then
      if prefs.save_bundle == true then
        -- Le nom choisi devient celui du fichier Lua ; le dossier Bundle porte
        -- le même nom (sans extension), avec audiofiles/ à l'intérieur.
        local parent = X.path_dir(f)
        local base = X.path_base(f)
        local stem = base:gsub("%.[^%.]*$", "")
        if stem == "" then stem = "ActionList" end
        local root = X.path_join(parent, stem)
        local saved, message = X.save_bundle(root, base)
        status = message
      else
        local file = io.open(f, "w")
        if file then
          file:write(X.ser({actions = actions, tabs = tabs, active_tab = active_tab, next_id = next_id, prefs = prefs}))
          file:close()
          status = "ActionList enregistrée : "..f
        else
          status = "Impossible d'écrire : "..f
        end
      end
    end
  end
  reaper.ImGui_SameLine(ctx)
  local cbundle, bundle_enabled = reaper.ImGui_Checkbox(ctx, "Bundle##save_bundle", prefs.save_bundle == true)
  if cbundle then prefs.save_bundle = bundle_enabled; X.save() end
  reaper.ImGui_SameLine(ctx)
  local icon_size = X.S(28)
  if reaper.ImGui_Button(ctx, "↶##undo", icon_size, icon_size) then X.undo_change() end
  reaper.ImGui_SameLine(ctx)
  if reaper.ImGui_Button(ctx, "↷##redo", icon_size, icon_size) then X.redo_change() end
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_Button(), 0xB22222FF)
  if reaper.ImGui_Button(ctx, "STOP (Échap)") then auto_chain = nil; X.fire_stop({dur = stop_fade}) end
  reaper.ImGui_PopStyleColor(ctx)
  reaper.ImGui_SameLine(ctx)
  reaper.ImGui_SetNextItemWidth(ctx, X.S(80))
  local cf, sf = reaper.ImGui_InputDouble(ctx, "Fade stop (s)", stop_fade)
  if cf then
    stop_fade = math.max(0, sf)
    reaper.SetExtState(EXT, "stopfade", tostring(stop_fade), true)
  end

  reaper.ImGui_Separator(ctx)
  X.draw_prefs()

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
      local shift = select(1, X.mods_shift_multi())
      if shift then
        pick_anchor = pick_anchor or sel_i
        selected = actions[sel_i+1].id
        X.pick_range(pick_anchor, sel_i+1)
      else
        X.pick_only(actions[sel_i+1], sel_i+1)
      end
    elseif sel_i and reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_UpArrow()) and actions[sel_i-1] then
      local shift = select(1, X.mods_shift_multi())
      if shift then
        pick_anchor = pick_anchor or sel_i
        selected = actions[sel_i-1].id
        X.pick_range(pick_anchor, sel_i-1)
      else
        X.pick_only(actions[sel_i-1], sel_i-1)
      end
    end
  end

  reaper.ImGui_Separator(ctx)
  
  local _, avail_h = reaper.ImGui_GetContentRegionAvail(ctx)
  local win_h_now = select(2, reaper.ImGui_GetWindowSize(ctx))
  -- Panneau de paramètres : moitié de la fenêtre par défaut (ajustable avec la poignée ⋮⋮),
  -- réduit quand aucune action n'est affichée ou que l'en-tête est replié.
  local lower_total = X.ed_open and (lower_h_override or math.floor(win_h_now * 0.5)) or X.S(70)
  local list_h = math.max(X.S(120), avail_h - lower_total - X.S(8))

  local table_flags = reaper.ImGui_TableFlags_RowBg() |
                      reaper.ImGui_TableFlags_BordersInnerV() |
                      reaper.ImGui_TableFlags_Resizable() |
                      reaper.ImGui_TableFlags_Reorderable() |
                      reaper.ImGui_TableFlags_ScrollY()

  if reaper.ImGui_BeginTable(ctx, "actions_table", 9, table_flags, 0, list_h) then
    reaper.ImGui_TableSetupScrollFreeze(ctx, 0, 1)

    reaper.ImGui_TableSetupColumn(ctx, "N°", reaper.ImGui_TableColumnFlags_WidthFixed(), X.S(34))
    reaper.ImGui_TableSetupColumn(ctx, "Titre", reaper.ImGui_TableColumnFlags_WidthStretch())
    reaper.ImGui_TableSetupColumn(ctx, "Type", reaper.ImGui_TableColumnFlags_WidthFixed(), X.S(78))
    reaper.ImGui_TableSetupColumn(ctx, "Statut", reaper.ImGui_TableColumnFlags_WidthFixed(), X.S(104))
    reaper.ImGui_TableSetupColumn(ctx, "AUTO", reaper.ImGui_TableColumnFlags_WidthFixed(), X.S(48))
    reaper.ImGui_TableSetupColumn(ctx, "FOLLOW", reaper.ImGui_TableColumnFlags_WidthFixed(), X.S(58))
    reaper.ImGui_TableSetupColumn(ctx, "DELAY (s)", reaper.ImGui_TableColumnFlags_WidthFixed(), X.S(86))
    reaper.ImGui_TableSetupColumn(ctx, "Output", reaper.ImGui_TableColumnFlags_WidthFixed(), X.S(170))
    reaper.ImGui_TableSetupColumn(ctx, "ID", reaper.ImGui_TableColumnFlags_WidthFixed(), X.S(54))

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
          local _, del_mod = X.mods_shift_multi()
          if del_mod then
            delete_row = i -- supprimé après la boucle d'affichage
          else
            selected = a.id
          end
        end
        reaper.ImGui_PopStyleColor(ctx)
        if number_bg then reaper.ImGui_PopStyleColor(ctx, 3) end
        drag_row(i, a)

        reaper.ImGui_TableSetColumnIndex(ctx, 1)
        local title_text = tostring(a.name or "")
        -- Un STOP ciblé affiche les titres des cues cibles, pas leurs IDs.
        -- La saisie/capture des cibles reste basée sur les IDs, qui sont stables.
        -- Si l'utilisateur a renommé la ligne manuellement (a.custom_title = true),
        -- on conserve son titre et on ne recalcule pas à partir des cibles.
        if not a.custom_title then
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
                  if tostring(target_action.id) == tostring(target_id) and X.is_playable_cue(target_action) then
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
            for _, target_id in ipairs(X.resolve_targets(a) or {}) do
              local found_name
              for _, tab in ipairs(tabs or {}) do
                for _, target_action in ipairs(tab.actions or {}) do
                  if tostring(target_action.id) == tostring(target_id) and X.is_playable_cue(target_action) then
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
        end
        local renaming = X.rename and X.rename.id == a.id
        if renaming then
          -- Renommage en place : Entrée / clic ailleurs = valider, Échap = annuler.
          if X.rename.focus then reaper.ImGui_SetKeyboardFocusHere(ctx); X.rename.focus = false end
          reaper.ImGui_SetNextItemWidth(ctx, -1)
          local rflags = reaper.ImGui_InputTextFlags_AutoSelectAll()
          local _, rtxt = reaper.ImGui_InputText(ctx, "##rename" .. tostring(a.id), X.rename.buf, rflags)
          X.rename.buf = rtxt
          if reaper.ImGui_IsItemDeactivated(ctx) or reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Enter(), false)
             or reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_KeypadEnter(), false) then
            if reaper.ImGui_IsKeyPressed(ctx, reaper.ImGui_Key_Escape(), false) then
              status = "Renommage annulé."
            else
              local nm = tostring(X.rename.buf or ""):gsub("^%s+", ""):gsub("%s+$", "")
              -- Comparaison avec title_text (nom réellement affiché) et non a.name :
              -- pour STOP/PAUSE/DEVAMP le nom affiché peut différer du a.name interne.
              -- Valider sans rien changer = pas de save.
              if nm ~= "" and nm ~= title_text then
                a.name = nm
                a.custom_title = true
                X.save()
                status = "Renommé : " .. nm
              end
            end
            X.rename = nil
          end
        else
          if reaper.ImGui_Selectable(ctx, title_text .. "##nm", picked[a.id] or false) then
            -- Le clic sur le titre ne change NI la cue préparée NI l'éditeur :
            -- il ne gère que la sélection multiple (captures de cibles).
            -- Sélection Windows : clic simple = remplacer, Ctrl = basculer,
            -- Maj = étendre depuis l'ancre. Ne déclenche jamais la cue.
            local shift, multi = X.mods_shift_multi()
            if shift then
              local anchor = pick_anchor
              if not anchor or not actions[anchor] then anchor = i end
              X.pick_range(anchor, i)
            elseif multi then
              if picked[a.id] then picked[a.id] = nil else picked[a.id] = true end
              pick_anchor = i
            else
              -- La sélection du titre ne change pas la cue préparée (selected).
              picked = {[a.id] = true}
              pick_anchor = i
            end
          end
          -- Double-clic sur le titre : renommer (désormais pour TOUS les types,
          -- y compris STOP / PAUSE / DEVAMP).
          if reaper.ImGui_IsItemHovered(ctx) and reaper.ImGui_IsMouseDoubleClicked(ctx, 0) then
            X.rename = {id = a.id, buf = title_text, focus = true}
          end
        end
        -- Déposer un fichier audio sur le titre crée une nouvelle cue juste après cette ligne.
        X.accept_audio_file_drop_create(i)

        reaper.ImGui_TableSetColumnIndex(ctx, 2)
        local type_label = X.TYPE_LABEL[a.type] or "?"
        if a.type == "stop" and (tonumber(a.dur) or 0) > 0 then type_label = "FADEOUT" end
        local lx, ly = reaper.ImGui_GetCursorScreenPos(ctx)
        reaper.ImGui_Text(ctx, type_label)
        if a.type == "osc" or a.type == "midi" then
          local tw = reaper.ImGui_CalcTextSize(ctx, type_label)
          local lh = reaper.ImGui_GetTextLineHeight(ctx)
          local cx, cy = lx + tw + X.S(10), ly + lh * 0.5
          local t_led = X.led[a.id]
          local lit = t_led and (reaper.time_precise() - t_led) < 0.25
          local ldl = reaper.ImGui_GetWindowDrawList(ctx)
          local is_midi = a.type == "midi"
          if lit then
            reaper.ImGui_DrawList_AddCircleFilled(ldl, cx, cy, X.S(6), is_midi and 0x3DA5FF55 or 0xFF3B3B55)
            reaper.ImGui_DrawList_AddCircleFilled(ldl, cx, cy, X.S(4), is_midi and 0x4DB3FFFF or 0xFF4A4AFF)
          else
            reaper.ImGui_DrawList_AddCircleFilled(ldl, cx, cy, X.S(4), is_midi and 0x14304DFF or 0x4A1616FF)
          end
          reaper.ImGui_DrawList_AddCircle(ldl, cx, cy, X.S(4), 0x00000099, 0, 1)
        end

        reaper.ImGui_TableSetColumnIndex(ctx, 3)
        local st = X.is_playable_cue(a) and active_ids[tostring(a.id)] or nil
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
        if reaper.ImGui_Button(ctx, lbl, X.S(48), 0) then X.fire(a) end
        if col then reaper.ImGui_PopStyleColor(ctx) end
        -- Petit STOP individuel dans la colonne Statut : il cible l'ID de cette cue
        -- sans modifier la cue préparée ni la sélection multiple.
        reaper.ImGui_SameLine(ctx, 0, X.S(3))
        if X.is_playable_cue(a) then
          if reaper.ImGui_SmallButton(ctx, "■##stopcue" .. tostring(a.id)) then
            X.stop_targets({a.id}, stop_fade)
            stop_until[a.id] = reaper.time_precise() + stop_fade + 0.2 + margin/1000
          end
        else
          -- Réserver l'espace pour garder l'alignement des boutons de statut.
          reaper.ImGui_Dummy(ctx, X.S(18), X.S(1))
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
          X.save()
        end

        reaper.ImGui_TableSetColumnIndex(ctx, 5)
        local changed_follow, new_follow = reaper.ImGui_Checkbox(ctx, "##follow_row_" .. tostring(a.id), a.follow == true)
        if changed_follow then
          a.follow = new_follow
          if new_follow then a.auto = false end
          X.save()
        end

        reaper.ImGui_TableSetColumnIndex(ctx, 6)
        reaper.ImGui_SetNextItemWidth(ctx, -1)
        local changed_delay, new_delay = reaper.ImGui_InputDouble(ctx, "##delay_row_" .. tostring(a.id), tonumber(a.delay) or 0, 0, 0, "%.2f")
        if changed_delay then a.delay = math.max(0, new_delay); X.save() end

        reaper.ImGui_TableSetColumnIndex(ctx, 7)
        -- Menu déroulant de piste directement dans la liste (cues audio/région et MIDI).
        local inplace_row = X.is_region_cue(a) and a.projfn and a.projfn ~= "" and not a.copy
        local row_has_track = ((X.is_file_cue(a) or X.is_region_cue(a)) and not inplace_row) or a.type == "midi"
        if row_has_track then
          reaper.ImGui_SetNextItemWidth(ctx, -1)
          local tc, tg = X.track_combo("##out_row_" .. tostring(a.id), a.track, X.is_region_cue(a))
          if tc then
            a.track = tg
            X.save()
            local trn = tg and X.find_track(tg)
            status = "Piste de Q" .. tostring(a.id) .. " : " .. (trn and X.track_name(trn) or "(piste d'origine)")
          end
        else
        local tr = X.find_track(a.track)
        local cible = tr and X.track_name(tr) or (X.is_file_cue(a) and "(choisir)" or (X.is_region_cue(a) and "(origine)" or "-"))
        if a.type == "snapshot" then
          X.ensure_snap(a)
          cible = a.snap and (#a.snap.order.." piste(s)") or "-"
          if a.projfn and a.projfn ~= "" then
            local base = a.projfn:match("([^/\\]+)$") or a.projfn
            cible = cible .. " → " .. base
          end
        elseif a.type == "stop" or a.type == "pause" or a.type == "devamp" then
          local ids = X.resolve_targets(a)
          cible = ids and (#ids.." cue(s)") or "toutes"
          if a.has_snapshot and a.snap_projfn and a.snap_projfn ~= "" then
            local base = a.snap_projfn:match("([^/\\]+)$") or a.snap_projfn
            cible = cible .. " + snapshot → " .. base
          end
        elseif a.type == "osc" then
          cible = a.port_name ~= "" and a.port_name or "(port)"
        elseif a.type == "midi" then
          cible = tr and X.track_name(tr) or "(piste)"
        end
        -- Pour AUDIO/REGION, projet du snapshot lié s'il est défini.
        if X.is_playable_cue(a) and a.has_snapshot and a.snap_projfn and a.snap_projfn ~= "" then
          local base = a.snap_projfn:match("([^/\\]+)$") or a.snap_projfn
          cible = cible .. " + snapshot → " .. base
        end
        reaper.ImGui_Text(ctx, cible)
        end

        reaper.ImGui_TableSetColumnIndex(ctx, 8)
        reaper.ImGui_Text(ctx, tostring(a.id or "?"))
        reaper.ImGui_PopID(ctx)
      end
      if move_from and move_to then X.move_rows(move_from, move_to) end
      if delete_row and actions[delete_row] then
        local da = actions[delete_row]
        picked[da.id] = nil
        table.remove(actions, delete_row)
        if selected == da.id then
          local nxt = actions[math.min(delete_row, #actions)]
          if nxt then X.pick_only(nxt, math.min(delete_row, #actions))
          else selected, pick_anchor = nil, nil end
        end
        sel_i = nil
        for k, x in ipairs(actions) do if x.id == selected then sel_i = k; break end end
        X.save()
        status = "Action supprimée : " .. tostring(da.name or da.id)
      end
    end
    reaper.ImGui_EndTable(ctx)
  end

  -- Cible de dépôt au niveau du tableau lui-même (pas de case dédiée).
  -- Les titres restent des cibles prioritaires pour insérer après une cue ;
  -- déposer sur le tableau hors d'un titre ajoute à la fin.
  X.accept_audio_file_drop_create(#actions)

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
  reaper.ImGui_InvisibleButton(ctx, "##resize_action_editor", sep_w, X.S(12))
  local sep_hover = reaper.ImGui_IsItemHovered(ctx)
  local sep_active = reaper.ImGui_IsItemActive(ctx)
  if sep_hover or sep_active then
    if reaper.ImGui_SetMouseCursor and reaper.ImGui_MouseCursor_ResizeNS then
      reaper.ImGui_SetMouseCursor(ctx, reaper.ImGui_MouseCursor_ResizeNS())
    end
  end
  if sep_active and reaper.ImGui_IsMouseDown(ctx, X.C_LEFT) then
    local _, mouse_y = reaper.ImGui_GetMousePos(ctx)
    local _, window_y = reaper.ImGui_GetWindowPos(ctx)
    local _, window_h = reaper.ImGui_GetWindowSize(ctx)
    -- mouse_y indique la limite supérieure du panneau inférieur.
    lower_h_override = math.max(X.S(110), math.min(window_h - X.S(160), window_y + window_h - mouse_y))
  end
  local sep_dl = reaper.ImGui_GetWindowDrawList(ctx)
  local sep_col = sep_active and 0x4FA3D1FF or (sep_hover and 0x7FA8C8FF or 0x606060FF)
  reaper.ImGui_DrawList_AddRectFilled(sep_dl, sep_x, sep_y, sep_x + sep_w, sep_y + X.S(12),
    (sep_hover or sep_active) and 0x303B46FF or 0x252525FF)
  reaper.ImGui_DrawList_AddLine(sep_dl, sep_x, sep_y + X.S(6), sep_x + sep_w, sep_y + X.S(6), sep_col, X.S(2))
  reaper.ImGui_DrawList_AddText(sep_dl, sep_x + sep_w * 0.5 - X.S(18), sep_y, sep_col, "⋮⋮")

  if sel_i then
    local open_ed = reaper.ImGui_CollapsingHeader(ctx, "Paramètres de l'action sélectionnée##edhdr", nil, reaper.ImGui_TreeNodeFlags_DefaultOpen())
    X.ed_open = open_ed and true or false
    if open_ed then
      -- Défilement vertical dédié aux paramètres (comme la liste du haut).
      local win_h = select(2, reaper.ImGui_GetWindowSize(ctx))
      local params_h = math.max(X.S(90), (lower_h_override or math.floor(win_h * 0.5)) - X.S(75))
      if reaper.ImGui_BeginChild(ctx, "##params_scroll", 0, params_h) then
        X.draw_editor(actions[sel_i], sel_i)
        reaper.ImGui_EndChild(ctx)
      end
    end
  else
    X.ed_open = false
  end

  reaper.ImGui_Separator(ctx)
  reaper.ImGui_Text(ctx, status)
end

---------------------------------------------------------------- Boucle principale
-- (pas de "local function" ici : limite Lua 200 locales au niveau module)
function X.loop()
  X.process_jobs()
  X.poll_midi_note_offs()
  X.process_auto_chain()
  reaper.ImGui_SetNextWindowSize(ctx, 720, 820, reaper.ImGui_Cond_FirstUseEver())
  local bg_col = X.interface_bg_color()
  local pushed_bg = 0
  local accent = X.accent_color()
  local pushed_accent = 0
  local function push_accent(slot_fn, col)
    if slot_fn then reaper.ImGui_PushStyleColor(ctx, slot_fn(), col); pushed_accent = pushed_accent + 1 end
  end
  push_accent(reaper.ImGui_Col_Button, X.accent_variant(accent, -0.28))
  push_accent(reaper.ImGui_Col_ButtonHovered, X.accent_variant(accent, -0.12))
  push_accent(reaper.ImGui_Col_ButtonActive, X.accent_variant(accent, 0.08))
  push_accent(reaper.ImGui_Col_Header, X.accent_variant(accent, -0.30))
  push_accent(reaper.ImGui_Col_HeaderHovered, X.accent_variant(accent, -0.12))
  push_accent(reaper.ImGui_Col_HeaderActive, X.accent_variant(accent, 0.08))
  push_accent(reaper.ImGui_Col_FrameBgActive, X.accent_variant(accent, -0.18))
  push_accent(reaper.ImGui_Col_SliderGrab, accent)
  push_accent(reaper.ImGui_Col_SliderGrabActive, X.accent_variant(accent, 0.12))
  if bg_col then
    if reaper.ImGui_Col_WindowBg then reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_WindowBg(), bg_col); pushed_bg = pushed_bg + 1 end
    if reaper.ImGui_Col_ChildBg then reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_ChildBg(), bg_col); pushed_bg = pushed_bg + 1 end
    if reaper.ImGui_Col_PopupBg then reaper.ImGui_PushStyleColor(ctx, reaper.ImGui_Col_PopupBg(), bg_col); pushed_bg = pushed_bg + 1 end
  end
  local visible, open = reaper.ImGui_Begin(ctx, "Realive v1.5 — Actions##v2", true)
  if visible then
    if reaper.ImGui_SetWindowFontScale then reaper.ImGui_SetWindowFontScale(ctx, ui_scale) end
    X.draw()
    reaper.ImGui_End(ctx)
  end
  if pushed_bg > 0 then reaper.ImGui_PopStyleColor(ctx, pushed_bg) end
  if pushed_accent > 0 then reaper.ImGui_PopStyleColor(ctx, pushed_accent) end
  if open then reaper.defer(X.loop) end
end

X.load_data()
history_last = X.current_data_string()

-- Couper le métronome (40364 = Options: Toggle metronome).
-- Tentatives multiples car GetToggleCommandState peut renvoyer -1 au tout premier instant.
do
  local function metro_state()
    if reaper.GetToggleCommandStateEx then
      return reaper.GetToggleCommandStateEx(0, 40364)
    end
    return reaper.GetToggleCommandState(40364)
  end
  local st = metro_state()
  if st == 1 then
    reaper.Main_OnCommand(40364, 0)
  end
  -- SWS si disponible
  if reaper.SNM_SetIntConfigVar then
    reaper.SNM_SetIntConfigVar("projmetroen", 0)
  end
  -- Seconde passe différée (REAPER parfois pas prêt à l'init)
  reaper.defer(function()
    if metro_state() == 1 then
      reaper.Main_OnCommand(40364, 0)
    end
    if reaper.SNM_SetIntConfigVar then
      reaper.SNM_SetIntConfigVar("projmetroen", 0)
    end
  end)
  st = metro_state()
  status = (st == 1)
    and "Realive v1.5 — métronome encore ON (toggle échoué)."
    or "Realive v1.5 prêt — métronome off."
end

reaper.defer(X.loop)
