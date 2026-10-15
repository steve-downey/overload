#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
# Differential test: emit the model's C++ programs and compile each with every
# compiler. Each emitted file states what the model expects in its header,
# `// expect: well-formed` or `// expect: ill-formed`; a compiler that
# disagrees is a finding against the cited sentence (docs/decisions.md#test-oracle),
# recorded in differential/known-disagreements.txt as `<file> <compiler>` so
# that CI stays green until the finding is settled.
#
# Usage: scripts/differential.sh [compiler...]   (default: g++ clang++)
# Needs lake on PATH; the Makefile target `differential` arranges that.

set -uo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="${EMIT_DIR:-$root/.build/emitted}"
known="$root/differential/known-disagreements.txt"
std="${DIFF_STD:--std=c++23}"
compilers=("$@")
if [[ ${#compilers[@]} -eq 0 ]]; then
    compilers=(g++ clang++)
fi

rm -rf "$out"
mkdir -p "$out"
(cd "$root" && lake -q exe emit "$out") || exit 1

status=0
printf '%-40s %-14s' "program" "expect"
for cxx in "${compilers[@]}"; do printf ' %-14s' "$cxx"; done
printf '\n'
for src in "$out"/*.cpp; do
    name=$(basename "$src")
    expect=$(sed -n 's|^// expect: ||p' "$src" | head -1)
    printf '%-40s %-14s' "$name" "$expect"
    for cxx in "${compilers[@]}"; do
        if "$cxx" "$std" -fsyntax-only -I "$root/src" "$src" >"$src.$(basename "$cxx").log" 2>&1; then
            got=well-formed
        else
            got=ill-formed
        fi
        if [[ "$got" == "$expect" ]]; then
            printf ' %-14s' "agrees"
        elif grep -qx "$name $(basename "$cxx")" "$known" 2>/dev/null; then
            printf ' %-14s' "$got (known)"
        else
            printf ' %-14s' "$got"
            status=1
        fi
    done
    printf '\n'
done

if (( status )); then
    echo
    echo "a compiler disagrees with the model; file the finding against the cited sentence" >&2
    echo "and, once filed, list it in $known" >&2
fi
exit "$status"
