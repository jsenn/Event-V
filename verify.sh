#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

logs="logs"
mkdir -p "$logs"

if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
  group()    { echo "::group::$1"; }
  endgroup() { echo "::endgroup::"; }
  error()    { echo "::error::$1"; }
else
  group()    { echo "==> $1"; }
  endgroup() { :; }
  error()    { echo "ERROR: $1" >&2; }
fi

verify() {
  local label="$1" log="$2"
  shift 2

  group "$label"
  local status=0
  cargo verus build "$@" 2>&1 | tee "$log" || status=$?

  if grep -Eq 'error:|warning:' "$log"; then
    error "$label reported errors or warnings"
    return 1
  fi
  if (( status != 0 )); then
    error "$label: cargo verus build failed (exit $status)"
    return 1
  fi
  endgroup
}

verify "library" "$logs/verus.log"

for dir in examples/*/; do
  example="$(basename "$dir")"
  verify "example $example" "$logs/verus-$example.log" --example "$example"
done

echo "All verification passed."
