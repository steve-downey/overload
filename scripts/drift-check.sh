#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
# Drift check: every citation in the model names a section and paragraph that
# exist in the pinned draft, and, with --current, the cited paragraphs are
# compared with the draft's current main so that citations now pointing at
# different text are listed for re-examination (docs/decisions.md#draft-pin).
#
# Usage: scripts/drift-check.sh [--current]
# The draft is cloned shallowly into .build/draft (override with DRAFT_DIR).
# Needs lake on PATH; the Makefile target `drift-check` arranges that.

set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
work="${DRAFT_DIR:-$root/.build/draft}"
draft_url="${DRAFT_URL:-https://github.com/cplusplus/draft.git}"
current=0
if [[ "${1:-}" == "--current" ]]; then
    current=1
fi

read -r tag commit document < <(cd "$root" && lake -q exe citations --pin)

if [[ ! -d "$work/.git" ]]; then
    echo "cloning $draft_url at $tag into $work"
    git clone -q --depth 1 --branch "$tag" "$draft_url" "$work"
fi
head=$(git -C "$work" rev-parse HEAD)
if [[ "$head" != "$commit" ]]; then
    echo "drift-check: $work is at $head, but the pin says $tag is $commit" >&2
    exit 1
fi
echo "pinned text: $document ($tag, $commit)"

# section <dir> <stable-name>: the TeX of one section, to stdout.
section() {
    local dir="$1" name="$2" file
    file=$(grep -l "\\\\rSec[0-9]\\[$name\\]" "$dir"/source/*.tex | head -1 || true)
    [[ -n "$file" ]] || return 1
    awk -v n="$name" '
        $0 ~ "\\\\rSec[0-9]\\[" n "\\]" { p = 1; next }
        p && /^\\rSec[0-9]\[/ { exit }
        p { print }' "$file"
}

# paragraph <dir> <stable-name> <n>: the TeX of one paragraph, to stdout.
paragraph() {
    section "$1" "$2" | awk -v k="$3" '/^\\pnum/ { c++ } c == k { print }'
}

status=0
while read -r stable para; do
    if ! sec=$(section "$work" "$stable"); then
        echo "MISSING  [$stable]: no such section in $document"
        status=1
        continue
    fi
    count=$(grep -c '^\\pnum' <<<"$sec" || true)
    if (( para > count )); then
        echo "MISSING  [$stable]/$para: the section has $count paragraphs in $document"
        status=1
        continue
    fi
    echo "ok       [$stable]/$para"
done < <(cd "$root" && lake -q exe citations --list)

if (( current )); then
    git -C "$work" fetch -q --depth 1 origin main
    cur="$work/.current"
    rm -rf "$cur"
    git -C "$work" worktree add -q --detach "$cur" FETCH_HEAD
    echo "current text: $(git -C "$work" rev-parse --short FETCH_HEAD)"
    while read -r stable para; do
        pinned=$(paragraph "$work" "$stable" "$para" | md5sum)
        now=$(paragraph "$cur" "$stable" "$para" 2>/dev/null | md5sum || true)
        if [[ "$pinned" != "$now" ]]; then
            echo "MOVED    [$stable]/$para: the paragraph differs on main; re-examine what cites it"
            status=1
        fi
    done < <(cd "$root" && lake -q exe citations --list)
    git -C "$work" worktree remove --force "$cur"
fi

exit "$status"
