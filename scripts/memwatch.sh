#!/bin/bash
# Memory watchdog: when free memory (MemAvailable) drops below 3 GB, kill the largest `lean`
# process. Logs to stdout. Polls every 2 s.
LIMIT_KB=$((3 * 1024 * 1024))
while true; do
  avail=$(awk '/MemAvailable/ {print $2}' /proc/meminfo)
  if [ "$avail" -lt "$LIMIT_KB" ]; then
    pid=$(ps -eo pid,rss,comm --sort=-rss | awk '$3 ~ /^lean/ {print $1; exit}')
    if [ -n "$pid" ]; then
      echo "$(date +%T) MemAvailable=${avail}kB < 3GB: killing lean pid $pid"
      kill -9 "$pid"
      sleep 5
    fi
  fi
  sleep 2
done
