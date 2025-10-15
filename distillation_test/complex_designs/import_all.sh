#!/usr/bin/env bash
set -euo pipefail

LIST_FILE="repos.txt"
DEST_DIR="$(pwd)/external"   # full path target under complex_designs/
PARALLEL_JOBS=6

mkdir -p "$DEST_DIR"
tmpdir="$(mktemp -d)"

process_repo() {
  url="$1"
  name="$(basename "${url%.git}")"
  work="$tmpdir/$name"

  echo "==> Cloning $url"
  git clone --depth 1 --recurse-submodules --shallow-submodules -j8 "$url" "$work" >/dev/null 2>&1 || {
    echo "!! Clone failed for $url"
    return 1
  }

  dest="$DEST_DIR/$name"
  mkdir -p "$dest"

  echo "==> Copying files to $dest"
  rsync -a --delete \
    --exclude '.git/' \
    --exclude '.github/' \
    --exclude '.gitmodules' \
    "$work"/ "$dest"/

  echo "==> Done: $name"
}

export -f process_repo
export tmpdir DEST_DIR

if command -v xargs >/dev/null; then
  <"$LIST_FILE" xargs -n1 -P"$PARALLEL_JOBS" -I{} bash -lc 'process_repo "$@"' _ {}
else
  while IFS= read -r url; do
    process_repo "$url"
  done <"$LIST_FILE"
fi

rm -rf "$tmpdir"

echo
echo "✅ All repos copied into $DEST_DIR/"
echo "Next steps:"
echo "  cd ../../.."
echo "  git add distillation_test/complex_designs/external"
echo "  git commit -m \"Imported 20 CPU/GPU repos (snapshot, no history)\""
