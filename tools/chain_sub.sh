#!/bin/zsh
# Emit (sub form) then Lean-check a list of classes; emitter and checker run concurrently,
# one heavy process each. Usage: tools/chain_sub.sh D c1 c2 ...
D=$1; shift
CL=($@)
ST=logs/chain_sub_$D.status
: > $ST
(
  for c in $CL; do
    caffeinate -i nice -n 19 tools/memcap.sh 4000 .venv/bin/python tools/cert_all.py $D $c $c --force --sub \
      >> logs/chain_sub_emit_$D.jsonl 2> logs/cert_$c.stderr
    echo "$c $?" >> $ST
  done
) &
EPID=$!
for c in $CL; do
  while ! grep -q "^$c " $ST; do
    kill -0 $EPID 2>/dev/null || grep -q "^$c " $ST || { echo "emitter gone before $c"; break 2; }
    /bin/sleep 20
  done
  if grep -q "^$c 0$" $ST; then
    caffeinate -i nice -n 19 .venv/bin/python tools/check_split.py $D --jobs=1 --only=$c
  else
    echo "{\"cls\": $c, \"emit_failed\": true}"
  fi
done
wait $EPID
echo chain done
