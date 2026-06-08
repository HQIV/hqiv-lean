#!/usr/bin/env bash
# Build HTML API documentation (doc-gen4). Output: ${HOMEPAGE}/docs/
# Mirrors leanprover-community/docgen-action/scripts/build_docs.sh but pins doc-gen4 via Git
# (Lake no longer resolves leanprover/doc-gen4 from Reservoir in this setup).
set -euo pipefail

: "${NAME:?NAME not set (lake package name)}"
: "${DOCS_FACETS:?DOCS_FACETS not set (e.g. HQIVLeptonResonance:docs)}"
: "${HOMEPAGE:?HOMEPAGE not set (e.g. docs)}"

mkdir -p docbuild

LEAN_REV="$(cut -f 2 -d: < lean-toolchain)"

cat << EOF > docbuild/lakefile.toml
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "${NAME}"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
git = "https://github.com/leanprover/doc-gen4"
rev = "${LEAN_REV}"
EOF

cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 ~/.elan/bin/lake update "${NAME}"
~/.elan/bin/lake build ${DOCS_FACETS}

cd ../
mkdir -p "${HOMEPAGE}"
sudo chown -R runner "${HOMEPAGE}" 2>/dev/null || true
cp -r docbuild/.lake/build/doc "${HOMEPAGE}/docs"
