#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
# Probe beman.transpose's typeclasses for the accurate-members obligation,
# parametricity in the callable, and the placement of std instances. Each
# line of probes.txt and parametricity.txt is compiled as its
# own translation unit with each compiler, and classified as soft, valid or
# hard. A row is marked `!` when a compiler's outcome is not what the
# obligation requires.
#
# Usage: probes/library/run.sh <beman.transpose include dir> [compiler...]
# The recorded outcomes, and the commit they were taken at, are in
# docs/probes.md.

set -uo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
if [[ $# -lt 1 ]]; then
    echo "usage: $0 <beman.transpose include dir> [compiler...]" >&2
    exit 2
fi
include=$1
shift
compilers=("$@")
if [[ ${#compilers[@]} -eq 0 ]]; then
    compilers=(g++ clang++)
fi
std="${PROBE_STD:--std=c++23}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

classify() {
    # classify <compiler> <source>: soft | valid | hard
    local cxx="$1" src="$2" log
    log="$src.$(basename "$cxx").log"
    if "$cxx" "$std" -fsyntax-only -I"$include" -I"$script_dir" "$src" >"$log" 2>&1; then
        echo soft
    elif [[ $(grep -c "error:" "$log") -eq 1 ]] && grep "error:" "$log" | grep -q PROBE_TRUE; then
        echo valid
    else
        echo hard
    fi
}

read -r -a tables <<<"${PROBE_TABLES:-probes parametricity algorithms}"
for table in "${tables[@]}"; do
printf '\n%s.txt\n' "$table"
printf '%-36s %-8s' probe required
for cxx in "${compilers[@]}"; do printf ' %-12s' "$(basename "$cxx")"; done
printf '\n'
while IFS='|' read -r name required call; do
    [[ -z $name || $name == \#* ]] && continue
    src="$work/$name.cpp"
    printf '#include "prelude.hpp"\nPROBE(%s)\nint main() {}\n' "$call" >"$src"
    mark=" "
    printf '%-36s %-8s' "$name" "$required"
    for cxx in "${compilers[@]}"; do
        got=$(classify "$cxx" "$src")
        if [[ $required == any ]]; then
            [[ $got == hard ]] && mark="!"
        elif [[ $got != "$required" ]]; then
            mark="!"
        fi
        printf ' %-12s' "$got"
    done
    printf ' %s\n' "$mark"
done <"$script_dir/$table.txt"
done

printf '\nlate_array.cpp\n'
for v in P A C; do
    printf '  %s' "$v"
    for cxx in "${compilers[@]}"; do
        if "$cxx" "$std" -fsyntax-only -I"$include" -DVARIANT="'$v'" \
            "$script_dir/late_array.cpp" >"$work/late-$v.log" 2>&1; then
            printf ' %-12s' compiles
        else
            printf ' %-12s' error
        fi
    done
    printf '\n'
done

# Runtime probes: each prints its own table.
for prog in coherence state callable_state; do
    printf '\n%s.cpp\n' "$prog"
    for cxx in "${compilers[@]}"; do
        printf ' %s\n' "$(basename "$cxx")"
        if "$cxx" "$std" -I"$include" "$script_dir/$prog.cpp" \
            -o "$work/$prog" >"$work/$prog.log" 2>&1; then
            "$work/$prog"
        else
            echo "  does not compile"
        fi
    done
done
