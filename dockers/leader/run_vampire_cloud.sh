#!/bin/bash
/usr/sbin/sshd -D &

BASENAME="${0##*/}"
log () {
  echo "${BASENAME} - ${1}"
}

log "Running as master node in cloud setup"

ip=$(/sbin/ip -o -4 addr list eth0 | awk '{print $4}' | cut -d/ -f1)

echo "$ip" | cat > /tmp/pp
WORKERS=$1
while read worker 
do
  echo "Sending $worker the main IP address $ip"
  scp /tmp/pp $worker:/tmp
done < $WORKERS 

mkdir /tmp/status
echo "dummy" | cat > /tmp/status/dummy
while true
do
  echo "Check if workers ready"
  ls /tmp/status
  sleep 2
done

PROBLEM=$2

mkdir /tmp/results
availablecores=$(nproc)
log "master details -> $ip:$availablecores"

# We need to log the main IP so that we can collect it from the logs and give it to the child nodes
log "main IP: $ip"

# In this setup we don't need to know who the children are

# Run vampire in the background whilst checking if we have a result
echo "For now turn off vampire on master"
#/competition/vampire --mode smtcomp --ignore_missing on --bad_option off --cores 0 $PROBLEM &> /tmp/results/result_${ip} & 

# We should be terminated after 20 minutes but let's count down from 30 minutes just in case 
counter=1500
while [ $counter -gt 0 ]; do
    for f in /tmp/results/*
    do
      # In reality, a file should only exist in /tmp/results if there is a solution
      # but let's check if it contains a solution
      if grep -q "sat" $f; then
        cat < $f
        exit 0
      fi
    done
    sleep 1
    let counter=counter-1
done
