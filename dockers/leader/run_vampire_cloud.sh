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
NAME=$(echo $PROBLEM | rev | cut -d"/" -f2- | rev)
echo "$NAME" | cat > /tmp/problem_name
while read worker 
do
  echo "Sending $worker the problem and its name to $worker" 
  until scp $PROBLEM $worker:/tmp
  do
    echo "Trying to send problem to $worker"
  done
  until scp /tmp/problem_name $worker:/tmp
  do
    echo "Trying to send problem name to $worker"
  done
done < $WORKERS 

sleep 2
ls $NAME

availablecores=$(nproc)
log "master details -> $ip:$availablecores"

# We need to log the main IP so that we can collect it from the logs and give it to the child nodes
log "main IP: $ip"

# In this setup we don't need to know who the children are

# Run vampire in the background whilst checking if we have a result
/competition/vampire --mode smtcomp --ignore_missing on --bad_option off --cores 0 -t 0 $PROBLEM &> $NAME/result_${ip} & 

# We should be terminated after 20 minutes but let's count down from 30 minutes just in case 
counter=1500
while [ $counter -gt 0 ]; do
    for f in $NAME/result_*
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
