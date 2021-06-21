#!/usr/bin/env bash

set -x

aws --profile $1 ecs run-task --launch-type EC2 --cluster $2 --task-definition $3 --network-configuration \
"{
   \"awsvpcConfiguration\": {
      \"subnets\": [\"$4\"],
      \"securityGroups\": [\"$5\"]
   }
}" \
--overrides \
"{
  \"containerOverrides\": [{
    \"name\": \"$7\",
    \"environment\": [
        {
            \"name\":\"COMP_S3_PROBLEM_PATH\",
            \"value\": \"shared-entries/$6\"
        },
        {
            \"name\":\"S3_BKT\",
            \"value\":\"smtcomp-problems-for-testing\"
        }
    ]
  }]
}
"
