#!/usr/bin/env sh

i=0

while true;
do
  n=$((i+1))
  LASTDIR=`git diff --name-only HEAD~$i HEAD~$n | tail -n 1 | cut -f 1 -d'/'`
  i=$((i+1))

  if [ -d "$LASTDIR" ] && [ "$LASTDIR" != ".github" ]; then
    echo "latest=$LASTDIR"
    break
  else
    >&2 printf "The variant '$LASTDIR' skipped.\n"
  fi

  if [ $i -gt 20 ]; then
    exit 2
  fi
done
