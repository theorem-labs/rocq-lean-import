#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$ROOT/lean/fixtures/manifest.toml"
CACHE="${LEAN4EXPORT_CACHE:-$ROOT/.cache/lean4export}"

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

ALL=false
if [[ "${1:-}" == "--all" ]]; then
  ALL=true
  shift
fi

requested=("$@")

manifest_value() {
  local key="$1"
  awk -v key="$key" '
    $1 == key && $2 == "=" {
      value=$0
      sub(/^[^=]+=[[:space:]]*/, "", value)
      gsub(/"/, "", value)
      print value
      exit
    }
  ' "$MANIFEST"
}

REPOSITORY="$(manifest_value lean4export_repository)"
COMMIT="$(manifest_value lean4export_commit)"
TOOLCHAIN="$(manifest_value lean_toolchain)"

if [[ -z "$REPOSITORY" || -z "$COMMIT" || -z "$TOOLCHAIN" ]]; then
  echo "error: manifest missing lean4export_repository, lean4export_commit, or lean_toolchain" >&2
  exit 1
fi

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

selected_entries=()
matched_requested=()

while IFS='|' read -r name output kind module default; do
  if selected "$name" "$default"; then
    selected_entries+=("$name|$output|$kind|$module|$default")
    if (( ${#requested[@]} > 0 )); then
      matched_requested+=("$name")
    fi
  fi
done < <(emit_entries)

for req in "${requested[@]}"; do
  matched=false
  for name in "${matched_requested[@]}"; do
    if [[ "$req" == "$name" ]]; then
      matched=true
      break
    fi
  done
  if [[ "$matched" == false ]]; then
    echo "error: unknown dump requested: $req" >&2
    exit 1
  fi
done

if (( ${#selected_entries[@]} == 0 )); then
  echo "error: no dumps selected" >&2
  exit 1
fi

for tool in git lake lean elan; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: missing required tool: $tool" >&2
    exit 1
  fi
done

mkdir -p "$(dirname "$CACHE")"
if [[ ! -d "$CACHE/.git" ]]; then
  git clone "$REPOSITORY" "$CACHE"
fi

if ! git -C "$CACHE" cat-file -e "$COMMIT^{commit}" 2>/dev/null; then
  git -C "$CACHE" fetch origin "$COMMIT"
fi
git -C "$CACHE" checkout "$COMMIT"

ACTUAL_TOOLCHAIN="$(tr -d '\r\n' < "$CACHE/lean-toolchain")"
if [[ "$ACTUAL_TOOLCHAIN" != "$TOOLCHAIN" ]]; then
  echo "error: lean4export toolchain mismatch: expected $TOOLCHAIN, got $ACTUAL_TOOLCHAIN" >&2
  exit 1
fi

(cd "$CACHE" && lake build)

LOCAL_LAKE="$ROOT/lean/fixtures/lakefile.lean"
if [[ ! -f "$LOCAL_LAKE" ]]; then
  echo "error: missing local fixture Lake file: $LOCAL_LAKE" >&2
  exit 1
fi

generate_entry() {
  local name="$1"
  local output="$2"
  local kind="$3"
  local module="$4"
  local out outdir tmp

  out="$ROOT/$output"
  outdir="$(dirname "$out")"
  mkdir -p "$outdir"
  tmp="$(mktemp "$outdir/.${name}.XXXXXX.ndjson")"
  trap '[[ -z "${tmp:-}" ]] || rm -f "$tmp"' RETURN

  if ! case "$kind" in
      upstream_module)
        (cd "$CACHE" && lake env .lake/build/bin/lean4export "$module") > "$tmp"
        ;;
      local_module)
        (cd "$ROOT/lean/fixtures" && lake env "$CACHE/.lake/build/bin/lean4export" "$module") > "$tmp"
      ;;
      *)
        echo "error: unsupported dump kind for $name: $kind" >&2
        false
        ;;
    esac
  then
    rm -f "$tmp"
    tmp=""
    trap - RETURN
    return 1
  fi

  if [[ ! -s "$tmp" ]]; then
    echo "error: generated dump is empty: $output" >&2
    rm -f "$tmp"
    tmp=""
    trap - RETURN
    exit 1
  fi
  if ! head -n 1 "$tmp" | grep -q '"meta"'; then
    echo "error: generated dump lacks NDJSON metadata: $output" >&2
    rm -f "$tmp"
    tmp=""
    trap - RETURN
    exit 1
  fi
  mv "$tmp" "$out"
  tmp=""
  trap - RETURN
  echo "generated $output"
}

for entry in "${selected_entries[@]}"; do
  IFS='|' read -r name output kind module default <<< "$entry"
  generate_entry "$name" "$output" "$kind" "$module"
done
