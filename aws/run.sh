#!/bin/bash
/usr/sbin/sshd -D &

BASENAME="${0##*/}"
log () {
  echo "${BASENAME} - ${1}"
}

sleep 2
echo Downloading problem from S3: ${COMP_S3_PROBLEM_PATH}

if [[ "${COMP_S3_PROBLEM_PATH}" == *".xz" ]];
then
  aws s3 cp s3://${S3_BKT}/${COMP_S3_PROBLEM_PATH} test.smt2.xz
  unxz test.smt2.xz
else
  aws s3 cp s3://${S3_BKT}/${COMP_S3_PROBLEM_PATH} test.smt2
fi

# Node type is paralle if we are in parallel mode 
NODE_TYPE="parallel"

if [ -z ${AWS_BATCH_JOB_MAIN_NODE_INDEX} ]
then
  log "This is the cloud setup" 
  echo main node: ${AWS_BATCH_JOB_MAIN_NODE_INDEX}
  echo this node: ${AWS_BATCH_JOB_NODE_INDEX}
  if [ "${AWS_BATCH_JOB_MAIN_NODE_INDEX}" != "${AWS_BATCH_JOB_NODE_INDEX}" ]; then
    log "Running as a child node"
    NODE_TYPE="child"
  else
    log 'Running as the main node"
    NODE_TYPE="main"
  fi
else
  log "This is the parallel setup"
fi

run_parallel () {
  log "Running as parallel node"
  # Just run vampire
  vampire/aws/run_vampire_main.sh test.smt2
}

run_main () {
  log "Running as master node"

  mkdir /tmp/results

  ip=$(/sbin/ip -o -4 addr list eth0 | awk '{print $4}' | cut -d/ -f1)

  availablecores=$(nproc)
  log "master details -> $ip:$availablecores"

  # We need to log the main IP so that we can collect it from the logs and give it to the child nodes
  # when running in cloud mode. This does not harm us in parallel mode
  log "main IP: $ip"

  # In this setup we don't need to know who the children are

  # Run vampire in the background whilst checking if we have a result
  vampire/aws/run_vampire_main.sh test.smt2 &> /tmp/results/result_${ip} & 

  # We should be terminated after 20 minutes but let's count down from 30 minutes just in case 
  counter=1200
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
}

# Workers run vampire and send a proof to the main node if they find one 
run_worker () {
  # get own ip and num cpus
  #
  ip=$(/sbin/ip -o -4 addr list eth0 | awk '{print $4}' | cut -d/ -f1)

  availablecores=$(nproc)

  log "I am a child node -> $ip:$availablecores, reporting to the master node -> ${AWS_BATCH_JOB_MAIN_NODE_PRIVATE_IPV4_ADDRESS}"

  # In this setup the main node doesn't care who I am

  echo "Now running solver"
  vampire/aws/run_vampire_worker.sh ${ip} test.smt2 > result_${ip}

  cat < result_${ip}

  echo "Sending result, should only get here if have a solution as run_vampire_worker should not terminate otherwise" 
  until scp result_${ip} ${AWS_BATCH_JOB_MAIN_NODE_PRIVATE_IPV4_ADDRESS}:/tmp/results
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
  parallel)
    run_parallel "${@}:
    ;;

  main)
    run_main "${@}"
    ;;

  child)
    run_worker "${@}"
    ;;

  *)
    log $NODE_TYPE
    usage "Could not determine node type. Expected (main/child)"
    ;;
esac
