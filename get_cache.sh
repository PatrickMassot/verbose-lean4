#!/usr/bin/env sh

find . -path ./.lake -prune -o -name "*.lean" -exec grep -h "^import Mathlib\." {} \; | sed 's/import \(Mathlib\.[^[:space:]]*\)/\1/' | sed 's/ .*$//' | tr '.' '/' | sed 's/^//' | sed 's/$/\.lean/' | tr '\n' ' ' | xargs lake exe cache get

