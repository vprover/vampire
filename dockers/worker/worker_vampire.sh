#!/bin/bash
/usr/sbin/sshd -D &

BASENAME="${0##*/}"
log () {
  echo "${BASENAME} - ${1}"
}

echo "Child node starting, waiting for problem path"
pwd

# get own ip and num cpus
ip=$(/sbin/ip -o -4 addr list eth0 | awk '{print $4}' | cut -d/ -f1)
availablecores=$(nproc)

#MAIN_IP=$(jq .nodeIp competition/leader_node_status.json)
#echo "Try send ready to ${MAIN_IP}"

# We assume that leader is going to place the problem in /tmp/problem 
ls /tmp
while [ ! -f /tmp/problem ] 
do
  sleep 1
done

echo "problem found"


OUT=$(head -1 /tmp/problem_name)
# Let's tell the leader that we're ready
echo "I am ${ip} and ready" | cat > $OUT/ready_${ip}

log "I am a child node -> $ip:$availablecores, reporting to the master node -> ${MAIN_IP}, solving $OUT"

# In this setup the main node doesn't care who I am

echo "Now running solver"

IFS=. read -r a b c d <<< "$ip"
rand="$((a * 256 ** 3 + b * 256 ** 2 + c * 256 + d))"
echo "Using random number $rand"

competition/vampire --mode smtcomp --ignore_missing on --bad_option off --cores 0 -si on -rs on --random_seed $rand /tmp/problem > /tmp/result_${ip}

cat < /tmp/result_${ip}

echo "Sending result, should only get here if have a solution as run_vampire_worker should not terminate otherwise" 
cp /tmp/result_${ip} $OUT
ls $OUT

rm /tmp/pp
rm /tmp/result*

log "done! goodbye"
ps -ef | grep sshd
tail -f /dev/null
