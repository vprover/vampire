#!/bin/bash
/usr/sbin/sshd -D &

PATH="$PATH:/opt/openmpi/bin/"
BASENAME="${0##*/}"
log () {
  echo "${BASENAME} - ${1}"
}
HOST_FILE_PATH="/tmp/hostfile"

sleep 2
echo main node: ${AWS_BATCH_JOB_MAIN_NODE_INDEX}
echo this node: ${AWS_BATCH_JOB_NODE_INDEX}
echo Downloading problem from S3: ${COMP_S3_PROBLEM_PATH}

if [[ "${COMP_S3_PROBLEM_PATH}" == *".xz" ]];
then
  aws s3 cp s3://${S3_BKT}/${COMP_S3_PROBLEM_PATH} test.smt2.xz
  unxz test.smt2.xz
else
  aws s3 cp s3://${S3_BKT}/${COMP_S3_PROBLEM_PATH} test.smt2
fi

# Set child by default switch to main if on main node container
NODE_TYPE="child"
if [ "${AWS_BATCH_JOB_MAIN_NODE_INDEX}" == "${AWS_BATCH_JOB_NODE_INDEX}" ]; then
  log "Running synchronize as the main node"
  NODE_TYPE="main"
fi

# wait for all nodes to report
wait_for_nodes () {
  log "Running as master node"

  touch $HOST_FILE_PATH
  ip=$(/sbin/ip -o -4 addr list eth0 | awk '{print $4}' | cut -d/ -f1)

  availablecores=$(nproc)
  log "master details -> $ip:$availablecores"

  # We need to log the main IP so that we can collect it from the logs and give it to the child nodes
  log "main IP: $ip"
  echo "$ip" >> $HOST_FILE_PATH
  lines=$(ls -dq /tmp/hostfile* | wc -l)
  while [ "${AWS_BATCH_JOB_NUM_NODES}" -gt "${lines}" ]
  do
    cat $HOST_FILE_PATH
    lines=$(ls -dq /tmp/hostfile* | wc -l)
    log "$lines out of $AWS_BATCH_JOB_NUM_NODES nodes joined, check again in 1 second"
    sleep 1
  done


  # All of the hosts report their IP and number of processors. Combine all these
  # into one file with the following script:
  python3 vampire/aws/make_combined_hostfile.py ${ip}
  cat vampire/aws/combined_hostfile

  vampire/aws/run_vampire.sh ${ip} test.smt2
}

# Fetch and run a script
report_to_master () {
  # get own ip and num cpus
  #
  ip=$(/sbin/ip -o -4 addr list eth0 | awk '{print $4}' | cut -d/ -f1)


  availablecores=$(nproc)

  log "I am a child node -> $ip:$availablecores, reporting to the master node -> ${AWS_BATCH_JOB_MAIN_NODE_PRIVATE_IPV4_ADDRESS}"

  echo "$ip" >> $HOST_FILE_PATH${AWS_BATCH_JOB_NODE_INDEX}
  ping -c 3 ${AWS_BATCH_JOB_MAIN_NODE_PRIVATE_IPV4_ADDRESS}
  until scp $HOST_FILE_PATH${AWS_BATCH_JOB_NODE_INDEX} ${AWS_BATCH_JOB_MAIN_NODE_PRIVATE_IPV4_ADDRESS}:$HOST_FILE_PATH${AWS_BATCH_JOB_NODE_INDEX}
  do
    echo "Sleeping 5 seconds and trying again"
  done
  log "done! goodbye"
  ps -ef | grep sshd
  tail -f /dev/null
}
##
#
# Main - dispatch user request to appropriate function
log $NODE_TYPE
case $NODE_TYPE in
  main)
    wait_for_nodes "${@}"
    ;;

  child)
    report_to_master "${@}"
    ;;

  *)
    log $NODE_TYPE
    usage "Could not determine node type. Expected (main/child)"
    ;;
esac
