#!/bin/zsh
# Run a command with a cap on the physical memory footprint of its whole process tree.
# Every 3 s, sum `phys_footprint` over the tree; above the cap, kill the tree (by PID) and
# exit 137 with a message on stderr. macOS does not enforce RLIMIT_AS, hence the watchdog.
#
# Usage: tools/memcap.sh LIMIT_MB command [args...]
# Wrap it the usual way: caffeinate -i nice -n 19 tools/memcap.sh 4000 lake env lean F.lean
limit_mb=$1; shift
"$@" &
root=$!

tree() {  # the PIDs of $1 and all its descendants
  local p=$1
  echo $p
  for c in $(pgrep -P $p); do tree $c; done
}

footprint_mb() {  # summed phys_footprint (MB) of the given PIDs
  local tot=0 v u
  for p in "$@"; do
    read v u <<< "$(footprint -p $p 2>/dev/null | awk '/phys_footprint:/{print $2, $3; exit}')"
    [[ -z $v ]] && continue
    case $u in
      KB) v=$(( v / 1024 )) ;;
      GB) v=$(( v * 1024 )) ;;
    esac
    tot=$(( tot + ${v%.*} ))
  done
  echo $tot
}

while kill -0 $root 2>/dev/null; do
  pids=($(tree $root))
  mb=$(footprint_mb $pids)
  if (( mb > limit_mb )); then
    echo "memcap: footprint ${mb} MB > ${limit_mb} MB; killing PIDs ${pids}" >&2
    kill ${pids} 2>/dev/null
    sleep 2
    kill -9 ${pids} 2>/dev/null
    exit 137
  fi
  sleep 3
done
wait $root
