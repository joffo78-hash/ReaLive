# Realive

Système de cues pour REAPER, inspiré des workflows de régie.

## Installation et dépendances

- REAPER
- ReaImGui (à installer via ReaPack)
- Mavriq Lua Sockets 1.2 pour la fonction OSC, si celle-ci est utilisée

## État de compatibilité

Cette version est en préparation. La compatibilité complète avec Windows, macOS et Linux n'est pas encore certifiée.
La partie OSC du script recherche actuellement `socket/core.dll`, ce qui semble spécifique à Windows. Cette partie doit être adaptée et testée avant d'annoncer une compatibilité multiplateforme.

## ReaPack

Le dépôt est configuré pour générer `index.xml` automatiquement avec GitHub Actions et `reapack-index`.
Après publication, l'URL à ajouter dans ReaPack sera :

`https://github.com/joffo78-hash/Realive/raw/main/index.xml`

Ne partagez pas cette URL comme dépôt ReaPack avant d'avoir vérifié que l'action GitHub a réussi et que `index.xml` existe.
