# ReaLive

Système de cues pour REAPER, inspiré des workflows de régie.

## Installation et dépendances

- REAPER
- ReaImGui (à installer via ReaPack)
- Mavriq Lua Sockets 1.2 pour la fonction OSC, si celle-ci est utilisée

### Installer ReaLive avec ReaPack

1. Dans REAPER, ouvrez **Extensions → ReaPack → Import repositories**.
2. Ajoutez l'index ReaLive :
   `https://github.com/joffo78-hash/Realive/raw/main/index.xml`
3. Ouvrez **Extensions → ReaPack → Browse packages**.
4. Recherchez **ReaLive**, sélectionnez le script et installez-le.
5. Installez **ReaImGui** si nécessaire. Pour les fonctions OSC, installez également **Mavriq Lua Sockets 1.2** depuis son dépôt ReaPack.

## Soutenir le développement

ReaLive est un outil développé pour la régie de spectacle vivant. Si le projet vous est utile, vous pouvez soutenir son développement ici :

**[Offrir un café au développeur](https://buymeacoffee.com/joffo)**

## État de compatibilité

La compatibilité complète avec Windows, macOS et Linux n'est pas encore certifiée. Les fonctions OSC dépendent de Mavriq Lua Sockets ; leur compatibilité dépend notamment de la disponibilité de la bibliothèque native adaptée à votre système.

## Dépôt

Code source, versions et suivi du projet : https://github.com/joffo78-hash/Realive
