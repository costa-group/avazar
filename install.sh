#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

info() { echo "[INFO]  $*"; }

###############################################################################
# Prerequisites
###############################################################################

# libz3-dev is needed by the avazar_tool Rust crate (z3 = "0.20.0" uses pkg-config, not bundled)
sudo apt-get install -y libz3-dev

# Rust toolchain (needed for circom and avazar_tool)
if ! command -v cargo > /dev/null 2>&1; then
    info "Rust not found. Installing via rustup..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path
    # shellcheck source=/dev/null
    source "$HOME/.cargo/env"
fi
command -v cargo > /dev/null 2>&1 || { echo "[ERROR] Rust installation failed. Try: https://rustup.rs" >&2; exit 1; }

###############################################################################
# ffsol
###############################################################################

info "=== Building ffsol ==="

(cd "$REPO_ROOT/ffsol" && bash install.sh)

info "ffsol built: $REPO_ROOT/ffsol/src/ffsol"

###############################################################################
# circom
###############################################################################

info "=== Building circom ==="

(cd "$REPO_ROOT/circom" && cargo build --release)

info "circom built: $REPO_ROOT/circom/target/release/circom"

###############################################################################
# avazar_tool
###############################################################################

info "=== Building avazar_tool ==="

(cd "$REPO_ROOT/avazar_tool" && cargo build --release)

info "avazar built: $REPO_ROOT/avazar_tool/target/release/avazar"

###############################################################################
# llzk_cli
###############################################################################

info "=== Downloading llzk_cli ==="

mkdir -p "$REPO_ROOT/translator/lean"
curl -L -o "$REPO_ROOT/translator/lean/llzk_cli" \
    "https://costa.fdi.ucm.es/papers/costa/llzk_cli"
chmod +x "$REPO_ROOT/translator/lean/llzk_cli"

info "llzk_cli downloaded: $REPO_ROOT/translator/lean/llzk_cli"

###############################################################################
# Summary
###############################################################################

echo
echo "================================================================"
echo " Build complete. Binaries:"
echo "   ffsol   : $REPO_ROOT/ffsol/src/ffsol"
echo "   circom  : $REPO_ROOT/circom/target/release/circom"
echo "   avazar  : $REPO_ROOT/avazar_tool/target/release/avazar"
echo
echo " Add the following to your ~/.bashrc:"
echo "   export PATH=\$PATH:$REPO_ROOT/ffsol/src"
echo "   export PATH=\$PATH:$REPO_ROOT/circom/target/release"
echo "   export PATH=\$PATH:$REPO_ROOT/avazar_tool/target/release"
echo " (see above for ffsol-specific env vars printed by ffsol/install.sh)"
echo "================================================================"
