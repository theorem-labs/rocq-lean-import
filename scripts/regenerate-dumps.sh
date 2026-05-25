#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$ROOT/lean/fixtures/manifest.toml"
CACHE="${LEAN4EXPORT_CACHE:-$ROOT/.cache/lean4export}"
REF="master"
TOOLCHAIN="leanprover/lean4:v4.30.0-rc2"

usage() {
  cat <<'USAGE'
Usage: scripts/regenerate-dumps.sh [--all] [dump-name]

Regenerates maintained NDJSON dumps with lean4export.
Default mode regenerates manifest entries marked default=true.
--all includes expensive optional entries.
USAGE
}

if [[ "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

for tool in git lake lean elan; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: missing required tool: $tool" >&2
    exit 1
  fi
done

mkdir -p "$(dirname "$CACHE")"
if [[ ! -d "$CACHE/.git" ]]; then
  git clone https://github.com/leanprover/lean4export "$CACHE"
fi

git -C "$CACHE" fetch origin "$REF"
git -C "$CACHE" checkout FETCH_HEAD

ACTUAL_TOOLCHAIN="$(tr -d '\r\n' < "$CACHE/lean-toolchain")"
if [[ "$ACTUAL_TOOLCHAIN" != "$TOOLCHAIN" ]]; then
  echo "error: lean4export toolchain mismatch: expected $TOOLCHAIN, got $ACTUAL_TOOLCHAIN" >&2
  exit 1
fi

(cd "$CACHE" && lake build)

ALL=false
if [[ "${1:-}" == "--all" ]]; then
  ALL=true
  shift
fi

requested=("$@")

emit_entries() {
  awk '
    /^\[\[dump\]\]/ {
      if (name != "") print name "|" output "|" kind "|" module "|" default
      name=output=kind=module=default=""
      next
    }
    /^name = / { gsub(/"/, "", $3); name=$3; next }
    /^output = / { gsub(/"/, "", $3); output=$3; next }
    /^kind = / { gsub(/"/, "", $3); kind=$3; next }
    /^module = / { gsub(/"/, "", $3); module=$3; next }
    /^default = / { default=$3; next }
    END { if (name != "") print name "|" output "|" kind "|" module "|" default }
  ' "$MANIFEST"
}

selected() {
  local name="$1"
  local default="$2"
  if (( ${#requested[@]} > 0 )); then
    for req in "${requested[@]}"; do
      [[ "$req" == "$name" ]] && return 0
    done
    return 1
  fi
  [[ "$ALL" == true || "$default" == true ]]
}

LOCAL_LAKE="$ROOT/lean/fixtures/lakefile.lean"
if [[ ! -f "$LOCAL_LAKE" ]]; then
  echo "error: missing local fixture Lake file: $LOCAL_LAKE" >&2
  exit 1
fi

while IFS='|' read -r name output kind module default; do
  if ! selected "$name" "$default"; then
    continue
  fi
  out="$ROOT/$output"
  mkdir -p "$(dirname "$out")"
  case "$kind" in
    upstream_module)
      (cd "$CACHE" && lake env .lake/build/bin/lean4export "$module") > "$out"
      ;;
    local_module)
      (cd "$ROOT/lean/fixtures" && lake env "$CACHE/.lake/build/bin/lean4export" "$module") > "$out"
      ;;
    *)
      echo "error: unsupported dump kind for $name: $kind" >&2
      exit 1
      ;;
  esac
  if [[ ! -s "$out" ]]; then
    echo "error: generated dump is empty: $output" >&2
    exit 1
  fi
  if ! head -n 1 "$out" | grep -q '"meta"'; then
    echo "error: generated dump lacks NDJSON metadata: $output" >&2
    exit 1
  fi
  echo "generated $output"
done < <(emit_entries)
