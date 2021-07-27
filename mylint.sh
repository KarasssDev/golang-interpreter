#!/usr/bin/env sh

LASTDIR=$1

echo "Going to run tests in $PWD..."
echo -e "section_start:`date +%s`:Linting...\r\e[0KLinting..."

PKG_OPAM="$LASTDIR.opam"
if [ ! -f "$PKG_OPAM" ]; then
    echo "$PKG_OPAM does not exist. Exit"
    exit 1
fi

if [ "$(opam lint -s $PKG_OPAM)" != "" ]; then
  echo "File $PKG_OPAM is not updated well. Command 'opam lint -s $PKG_OPAM' should print nothing"
  opam lint $PKG_OPAM
else
  echo "Checking $PKG_OPAM passed."
fi
