#!/usr/bin/env bash
set -euo pipefail
LANG_NAME="sr"
PLUGIN_NAME="sr-treesitter"
PACK_BUCKET="${PACK_BUCKET:-$LANG_NAME}"
PREFIX="${PREFIX:-${XDG_DATA_HOME:-$HOME/.local/share}/nvim/site}"
TARGET="$PREFIX/pack/$PACK_BUCKET/start/$PLUGIN_NAME"

if [[ -d "$TARGET" ]]; then
  echo "Removing $TARGET"
  rm -rf "$TARGET"
  echo "Uninstalled."
else
  echo "Nothing to remove at $TARGET"
fi
