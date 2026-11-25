#!/bin/sh
# Builds the results without hypothesis (unconditional/Solution.lean).
#
# It downloads three repositories from github.com at fixed commits, applies the two compatibility patches of openai/math,
# copies the 7,283 files of the import closure of OAI.LinearAlgebra.SpectralBooks.EveryField into this project, checks
# their SHA-256 sums, and builds. It changes no file of this repository except by adding these copies.
# Needs: git, shasum or sha256sum, elan. Time: many hours on 8 cores; memory: some files need 7 GB or more each.
set -eu
cd "$(dirname "$0")/.."
W=unconditional/work
mkdir -p "$W"

clone() {
  if [ ! -d "$3/.git" ]; then git clone --quiet "$1" "$3"; fi
  git -C "$3" checkout --quiet "$2"
}
clone https://github.com/openai/math.git 3344da59991ed94f9ba711217b29c1d760badfa6 "$W/math"
clone https://github.com/ZIB-IOL/lemmata.git a2dd430f283febd755a6ee6932d0b0fdabfb330c "$W/lemmata"
clone https://github.com/harfe/fixed-point-theorems-lean4.git 770940ddf9878cf61952ed53d910b92bca841838 "$W/fpt"

patch() {
  P="$(pwd)/$W/math/lean/patches/$2"
  if git -C "$1" apply --reverse --check "$P" 2>/dev/null; then return 0; fi
  git -C "$1" apply "$P"
}
patch "$W/lemmata" lemmata-lean4341.patch
patch "$W/fpt" fixed-point-theorems-lean4341.patch

# copy the closure
while IFS="$(printf '\t')" read -r root path; do
  mkdir -p "$(dirname "$path")"
  cp "$W/$root/$path" "$path"
done < unconditional/closure.tsv

if command -v sha256sum >/dev/null 2>&1; then sha256sum -c --quiet unconditional/SHA256SUMS
else shasum -a 256 -c --quiet unconditional/SHA256SUMS; fi

lake exe cache get
lake build Unconditional
lake env lean unconditional/AxiomsU.lean
