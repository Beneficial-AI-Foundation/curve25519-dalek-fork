#!/usr/bin/env bash
# Install the charon + aeneas release pinned in lakefile.toml into .aeneas/.
set -euo pipefail
cd "$(dirname "$0")/.."

TAG=$(awk -F'"' '/^\[/{name=""} /^name = /{name=$2} /^rev = / && name=="aeneas"{print $2}' lakefile.toml)
: "${TAG:?no aeneas rev in lakefile.toml}"
# Linux x86_64 -> linux-x86_64, Linux aarch64 -> linux-aarch64, Darwin arm64 -> macos-aarch64
ASSET=aeneas-$(uname -sm | tr 'A-Z ' 'a-z-' | sed 's/darwin/macos/; s/arm64/aarch64/').tar.gz

valid_install() {
    local version
    version=$("$1/aeneas" -version 2>/dev/null) || return 1
    [[ "$version" == "aeneas $TAG" \
        && -x "$1/charon" && -x "$1/charon-driver" \
        && -s "$1/rust-toolchain" && -s "$1/backends/lean/lean-toolchain" ]]
}

if ! valid_install .aeneas; then
    tmp=$(mktemp -d .aeneas.XXXXXX)
    trap 'rm -rf "$tmp"' EXIT
    curl -fsSL --proto '=https' \
        "https://github.com/AeneasVerif/aeneas/releases/download/$TAG/$ASSET" \
        | tar -xz -C "$tmp"
    valid_install "$tmp"
    rm -rf .aeneas
    mv "$tmp" .aeneas
fi
# The nightly (with rustc-dev) that charon-driver was built against, per the bundle's rust-toolchain.
(cd .aeneas && rustup toolchain install --no-self-update)
cp .aeneas/backends/lean/lean-toolchain lean-toolchain
