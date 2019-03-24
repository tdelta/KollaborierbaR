#!/bin/bash


base=$1
branch=$2

bold() {
  echo "$(tput bold)$1$(tput sgr0)"
}

bold "Base branch: $base"
bold "Feature branch: $branch"

lastcommit="$(git rev-list --simplify-by-decoration -2 HEAD | head -1)"
parentOfFirst="$(git merge-base $branch $base)"

echo

bold "Parent of first commit: $parentOfFirst"
bold "Last commit on this branch: $lastcommit"

echo

bold "Commits on $branch":

commits=`git rev-list --no-merges --first-parent $branch --not $parentOfFirst`
printf '%s\n' "${commits[@]}"

echo

bold "List of modified files:"

for c in $commits; do
    git diff-tree --no-commit-id --name-only -r $c
done | sort | uniq

