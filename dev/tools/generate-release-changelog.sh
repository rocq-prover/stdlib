#!/usr/bin/env bash

set -e
set -o pipefail

ask_confirmation() {
    read -p "Continue anyway? [y/N] " "${quick_conf[@]}" -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    fi
}

if ! git diff --quiet; then
    echo "Warning: current tree is dirty."
    ask_confirmation
fi

changelog_entries_with_title=(doc/changelog/*/*.rst)

tmp=$(mktemp)
for f in "${changelog_entries_with_title[@]}"; do

    cat=${f%/*} # dirname
    if [[ ${f##*/} = 00000-title.rst ]]; then
        type=0
    else
        type_name=$(head -n 1 "$f" | cut -f 3 -d ' ')
        type_name=${type_name%".v\`"}
        type_name=${type_name#"\`"}
        type="1${type_name}"
    fi
    printf '%s %s %s\n' "$cat" "$type" "$f" >> "$tmp"
done

while read -r _ type f; do
    cat "$f" >> released.rst
    echo "" >> released.rst
    if ! [[ $type = 0 ]]; then git rm "$f" >> /dev/null; fi
done < <(sort "$tmp")

echo
echo "Changelog written in released.rst. Move its content to a new section in doc/sphinx/changes.rst."
