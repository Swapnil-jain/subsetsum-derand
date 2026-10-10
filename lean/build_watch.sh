#!/usr/bin/env bash
# Low-memory local Lean build: nice -n 19, one Lean thread (lakefile.toml), RSS watchdog.
#   build_watch.sh [lake args...]      e.g. build_watch.sh build SubsetsumLean.Stage1Points
# Every 1 s it sums the RSS of all lean/lake processes started under this script; above LIMIT_MB (default 3072)
# it kills the build and exits 3. Peak RSS (MB) is printed at the end and appended to build_peak.log.
set -u
LIMIT_MB=${LIMIT_MB:-3072}
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin
export PATH=$TC:$PATH
cd "$(dirname "$0")"
[ $# -ge 1 ] || set -- build
# A bare `build` would let lake run independent modules in parallel (two Lean processes, above 3 GB here), so
# build the modules one at a time, in import order.
if [ $# -eq 1 ] && [ "$1" = build ]; then
  for m in Basic Stage1Defs Stage1Points Stage1 Stage2Defs Stage2 ExplicitDefs Explicit ExplicitN0Defs ExplicitAnchors ExplicitN0; do
    "$0" build "SubsetsumLean.$m" || exit $?
  done
  exec "$0" build SubsetsumLean
fi
# lake has no -j flag: --threads=1 is set in lakefile.toml, and modules are built one target at a time.
nice -n 19 lake "$@" &
PID=$!
peak=0
tree() { local p=$1; echo "$p"; for c in $(pgrep -P "$p"); do tree "$c"; done; }
while kill -0 $PID 2>/dev/null; do
  kb=0
  for p in $(tree $PID); do r=$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' '); kb=$((kb + ${r:-0})); done
  mb=$((kb / 1024)); [ $mb -gt $peak ] && peak=$mb
  if [ $mb -gt "$LIMIT_MB" ]; then
    echo "ABORT: RSS ${mb} MB > ${LIMIT_MB} MB"; for p in $(tree $PID); do kill -9 "$p" 2>/dev/null; done
    echo "$(date '+%F %T') ABORT peak ${peak} MB: lake $*" >> build_peak.log; exit 3
  fi
  sleep 1
done
wait $PID; rc=$?
echo "peak RSS ${peak} MB, exit $rc"
echo "$(date '+%F %T') rc=$rc peak ${peak} MB: lake $*" >> build_peak.log
exit $rc
