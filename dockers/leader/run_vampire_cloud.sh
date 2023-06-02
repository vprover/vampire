#!/bin/bash
/usr/sbin/sshd -D &

BASENAME="${0##*/}"
log () {
  echo "${BASENAME} - ${1}"
}

log "Running as master node in cloud setup"

ip=$(/sbin/ip -o -4 addr list eth0 | awk '{print $4}' | cut -d/ -f1)

WORKERS=$1
PROBLEM=$2
echo "$PROBLEM" | cat > /tmp/pp
while read worker 
do
  echo "Sending $worker the problem path" 
  until scp /tmp/pp $worker:/tmp
  do
    echo "Trying to send path to $worker"
  done
done < $WORKERS 

OUT=$(echo $PROBLEM | rev | cut -d"/" -f2- | rev)
sleep 2
ls $OUT

availablecores=$(nproc)
log "master details -> $ip:$availablecores"

# We need to log the main IP so that we can collect it from the logs and give it to the child nodes
log "main IP: $ip"

# In this setup we don't need to know who the children are

# Run vampire in the background whilst checking if we have a result
/competition/vampire --mode smtcomp --ignore_missing on --bad_option off --cores 0 -t 0 $PROBLEM &> $OUT/result_${ip} & 

# We should be terminated after 20 minutes but let's count down from 30 minutes just in case 
counter=1500
while [ $counter -gt 0 ]; do
    for f in $OUT/result_*
    do
      # Let's check if it contains a solution
      if grep -q "sat" $f; then
        cat < $f
        exit 0
      fi
    done
    sleep 1
    let counter=counter-1
done
