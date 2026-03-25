#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

log() {
  printf '\n[setup-codex] %s\n' "$*"
}

die() {
  printf '\n[setup-codex] error: %s\n' "$*" >&2
  exit 1
}

need_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    die "missing required command: $1"
  fi
}

log "Bootstrapping VCV-io for Codex"

need_cmd git

if ! command -v elan >/dev/null 2>&1; then
  need_cmd curl
  log "Installing elan"
  if ! curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --default-toolchain none; then
    die "failed to install elan; rerun with network access"
  fi
fi

elan_env="${HOME}/.elan/env"
if [ -f "$elan_env" ]; then
  # shellcheck disable=SC1090
  . "$elan_env"
fi

need_cmd elan
need_cmd lake
need_cmd cc

toolchain="$(tr -d '\r\n' < lean-toolchain)"
log "Ensuring Lean toolchain ${toolchain}"
elan toolchain install "$toolchain"

if [ -f .gitmodules ]; then
  log "Syncing declared git submodules"
  while read -r _ submodule_path; do
    [ -n "${submodule_path:-}" ] || continue
    git submodule sync -- "$submodule_path"
    git submodule update --init --recursive -- "$submodule_path"
  done < <(git config --file .gitmodules --get-regexp '^submodule\..*\.path$' || true)
  if [ ! -f third_party/mlkem-native/mlkem/mlkem_native.c ]; then
    die "third_party/mlkem-native is still missing after submodule sync"
  fi
fi

log "Fetching Mathlib cache"
if ! lake exe cache get; then
  die "failed to fetch Mathlib cache; rerun with network access"
fi

if [ "${VCVIO_CODEX_FULL_BUILD:-0}" = "1" ]; then
  log "Running full VCV-io build"
  lake build

  log "Checking VCVio.lean in the project environment"
  lake env lean VCVio.lean

  log "Running smoke test"
  lake env lean VCVioTest/Smoke.lean
else
  log "Skipping full build; set VCVIO_CODEX_FULL_BUILD=1 to enable it"
fi

log "Codex environment is ready"
printf 'Next file to open: %s\n' "Examples/OneTimePad.lean"
