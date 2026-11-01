#!/usr/bin/env bash
# Install the pinned Verus release (verus, cargo-verus, z3) and its Rust toolchain.
#
#   scripts/install-verus.sh            # install into $VERUS_HOME (default ~/.verus)
#   eval "$(scripts/install-verus.sh --print-env)"   # put it on PATH
#
# Idempotent: re-running with the same pinned version is a no-op.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=../verus-toolchain.env
source "$repo_root/verus-toolchain.env"

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)   platform=x86-linux ;;
  Linux-aarch64)  platform=arm64-linux ;;
  Darwin-arm64)   platform=arm64-macos ;;
  Darwin-x86_64)  platform=x86-macos ;;
  *) echo "install-verus: unsupported platform $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac

verus_home="${VERUS_HOME:-$HOME/.verus}"
install_dir="$verus_home/$VERUS_VERSION"
bin_dir="$install_dir/verus-$platform"

if [[ "${1:-}" == "--print-env" ]]; then
  echo "export PATH=\"$bin_dir:\$PATH\""
  exit 0
fi

if ! command -v rustup >/dev/null; then
  echo "install-verus: rustup is required (https://rustup.rs)" >&2
  exit 1
fi
rustup toolchain install "$RUST_TOOLCHAIN" --profile minimal --component rustfmt >&2

if [[ -x "$bin_dir/verus" && -x "$bin_dir/cargo-verus" ]]; then
  echo "install-verus: Verus $VERUS_VERSION already installed at $bin_dir" >&2
else
  asset="verus-$VERUS_VERSION-$platform.zip"
  url="https://github.com/verus-lang/verus/releases/download/release/$VERUS_VERSION/$asset"
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  echo "install-verus: downloading $url" >&2
  curl --fail --location --silent --show-error --retry 4 -o "$tmp/$asset" "$url"
  mkdir -p "$install_dir"
  (cd "$install_dir" && unzip -q -o "$tmp/$asset")
  if [[ "$platform" == *macos && -f "$bin_dir/macos_allow_gatekeeper.sh" ]]; then
    (cd "$bin_dir" && bash macos_allow_gatekeeper.sh)
  fi
fi

"$bin_dir/verus" --version >&2
echo "install-verus: add to PATH with: eval \"\$($0 --print-env)\"" >&2
