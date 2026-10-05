#!/usr/bin/env bash
set -euo pipefail

# Keep the generated revision out of Git so a clean build can name its own source commit.
repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
artifact_revision=$(git -C "$repo_root" rev-parse HEAD)
artifact_short=$(git -C "$repo_root" rev-parse --short=12 HEAD)
artifact_status=""
if [[ -n $(git -C "$repo_root" status --porcelain --untracked-files=normal) ]]; then
  artifact_status=" (modified working tree)"
fi
printf '\\renewcommand{\\artifactcommit}{%s}\n\\renewcommand{\\artifactshort}{%s}\n\\renewcommand{\\artifactstatus}{%s}\n' \
  "$artifact_revision" "$artifact_short" "$artifact_status" > "$repo_root/paper/revision.tex"

cd "$repo_root/paper"
exec latexmk -pdf -interaction=nonstopmode -halt-on-error frontier.tex
