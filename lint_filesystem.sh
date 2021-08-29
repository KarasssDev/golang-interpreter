#!/usr/bin/env sh

LASTDIR=$1

echo "Going to run tests in $PWD..."
echo -e "section_start:`date +%s`:Linting...\r\e[0KLinting..."

PKG_OPAM="$LASTDIR.opam"
if [ ! -f "$PKG_OPAM" ]; then
    echo "$PKG_OPAM does not exist. Exit"
    exit 1
fi

# A few warnings were disabled
# 21: Field 'opam-version' doesn't match the current version
OPAM_LINT_CMD="opam lint --warnings=-21-23 -s $PKG_OPAM"
if [ "$($OPAM_LINT_CMD)" != "" ]; then
  echo "File $PKG_OPAM is not updated well. Command '$OPAM_LINT_CMD' should print nothing"
  opam lint $PKG_OPAM
  if  [ "$LASTDIR" != "Lambda" ]; then
    exit 2
  fi
else
  echo "Checking $PKG_OPAM passed."
fi
