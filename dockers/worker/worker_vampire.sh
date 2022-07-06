#!/bin/bash
/usr/sbin/sshd -D &

BASENAME="${0##*/}"
log () {
  echo "${BASENAME} - ${1}"
}

echo "Child node starting, waiting for problem path"

# get own ip and num cpus
ip=$(/sbin/ip -o -4 addr list eth0 | awk '{print $4}' | cut -d/ -f1)
availablecores=$(nproc)

MAIN_IP=$(jq .ipVer leader_node_status.json)

echo "Try send ready to ${MAIN_IP}"

# Let's tell the leader that we're ready
echo "I am ${ip} and ready" | cat > /tmp/ready_${ip}
until scp /tmp/ready_${ip} ${MAIN_IP}:/tmp/status
do
  echo "Trying to send ready"
done 

# We assume that leader is going to create a file called pp containing the problem path
PROBLEM="none"
ls /tmp
while [ ! -f /tmp/pp ] 
do
  PROBLEM=$(head -n 1 /tmp/pp)
  echo "problem path $PROBLEM found"
done


log "I am a child node -> $ip:$availablecores, reporting to the master node -> ${MAIN_IP}, solving $PROBLEM"

# In this setup the main node doesn't care who I am

echo "Now running solver"

IFS=. read -r a b c d <<< "$ip"
rand="$((a * 256 ** 3 + b * 256 ** 2 + c * 256 + d))"
echo "Using random number $rand"

vampire --mode smtcomp --ignore_missing on --bad_option off --cores 0 -si on -rs on --random_seed $rand $PROBLEM > /tmp/result_${ip}

cat < /tmp/result_${ip}

echo "Sending result, should only get here if have a solution as run_vampire_worker should not terminate otherwise" 
until scp /tmp/result_${ip} ${MAIN_IP}:/tmp/results
do
    echo "Sleeping 5 seconds and trying again"
done

log "done! goodbye"
ps -ef | grep sshd
tail -f /dev/null
