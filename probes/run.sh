#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
# Compile every probe variant with each compiler and print the outcome table.
# Usage: probes/run.sh [compiler...]   (default: g++ clang++)
# Exit status is 0 whenever every compile ran; the table is the result. The
# plan's recorded outcomes are in docs/probes.md.

set -uo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
compilers=("$@")
if [[ ${#compilers[@]} -eq 0 ]]; then
    compilers=(g++ clang++)
fi
std="${PROBE_STD:--std=c++23}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

declare -A variants=(
    [step_order]="A B C D E G H I"
    [step_order_variable]="B"
    [tie_break]="A B C D"
    [constant_conversion]="A B"
)

outcome() {
    # outcome <compiler> <source> <variant>: compiles | hard error | wrong
    local cxx="$1" src="$2" v="$3" exe
    exe="$work/$(basename "$src" .cpp)-$v-$(basename "$cxx")"
    if "$cxx" "$std" -DVARIANT="'$v'" -o "$exe" "$src" >"$exe.log" 2>&1; then
        if "$exe"; then echo "compiles"; else echo "wrong candidate"; fi
    elif grep -q "ambiguous" "$exe.log"; then
        echo "ambiguous"
    else
        echo "hard error"
    fi
}

for probe in step_order step_order_variable tie_break constant_conversion; do
    src="$script_dir/$probe.cpp"
    printf '\n%s\n' "$probe"
    printf '%-8s' "variant"
    for cxx in "${compilers[@]}"; do printf '%-18s' "$cxx"; done
    printf '\n'
    for v in ${variants[$probe]}; do
        printf '%-8s' "$v"
        for cxx in "${compilers[@]}"; do
            printf '%-18s' "$(outcome "$cxx" "$src" "$v")"
        done
        printf '\n'
    done
done
