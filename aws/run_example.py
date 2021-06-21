#!/usr/bin/env python3

import argparse
import json
import subprocess
from time import sleep
import re
import string

import boto3
#import botocore_amazon.monkeypatch

class LogAnalyzer:
    def __init__(self, cloudwatch):
        self.cloudwatch = cloudwatch

    def get_log_group(self, solver_name):
        return f"/ecs/{solver_name}"

    def get_log_stream(self, solver_name, task_id):
        return f"ecs/{solver_name}/{task_id}"

    def fetch_logs(self, solver_name, task_id):
        log_group_name = self.get_log_group(solver_name)
        log_stream_name = self.get_log_stream(solver_name, task_id)
        log = ""
        try:
            events_obj = self.cloudwatch.get_log_events(logGroupName=log_group_name,
                                                        logStreamName=log_stream_name,
                                                        startFromHead=False)
        except Exception as e:
            # print("Task logs don't exist yet")
            return None
        cur_token = None
        while events_obj["nextBackwardToken"] != cur_token:
            cur_token = events_obj["nextBackwardToken"]

            for e in events_obj["events"]:
                log += f"{e['message']}\n"
            events_obj = self.cloudwatch.get_log_events(logGroupName=log_group_name,
                                                        logStreamName=log_stream_name,
                                                        nextToken=events_obj["nextBackwardToken"],
                                                        startFromHead=False)
        return log


    def get_ip_address(self, solver_name, task_arn):
        log_group_name = self.get_log_group(solver_name)
        log_stream_name = self.get_log_stream(solver_name, task_arn)
        print(f"Getting ip address from logs in {log_group_name}/{log_stream_name}")
        try:
            events_obj = self.cloudwatch.get_log_events(logGroupName=log_group_name,
                                                        logStreamName=log_stream_name,
                                                        startFromHead=False)
        except Exception as e:
            print("Task logs don't exist yet")
            return None
        cur_token = None
        while events_obj["nextBackwardToken"] != cur_token:
            cur_token = events_obj["nextBackwardToken"]
            print(cur_token)
            for e in events_obj["events"]:
                print(e)
                if "main IP:" in e["message"]:
                    return e["message"].split("main IP:")[1].replace(" ", "")
            events_obj = self.cloudwatch.get_log_events(logGroupName=log_group_name,
                                                        logStreamName=log_stream_name,
                                                        nextToken=events_obj["nextBackwardToken"],
                                                        startFromHead=False)
        return None

class IpFetch:
    def __init__(self, log_analyzer):
        self.log_analyzer = log_analyzer

    def fetch_ip(self, solver_name, task_id):
        while True:
            s = self.log_analyzer.get_ip_address(solver_name, task_id)
            if s is not None:
                return s
            sleep(5)


class Task:
    def __init__(self, ecs_client=None, cluster_name=None, task_arn=None):
        self.ecs_client = ecs_client
        self.cluster_name = cluster_name
        self.task_arn = task_arn

    def kill(self):
        self.ecs_client.stop_task(
            cluster=self.cluster_name,
            task=self.task_arn,
            reason='Main node completed')

    def task_completed(self):
        described = self.ecs_client.describe_tasks(cluster=self.cluster_name, tasks=[self.task_arn])["tasks"][0]
        return described['lastStatus'] == "STOPPED"

    def wait_for_task_complete(self):
        while True:
            if self.task_completed():
                print("Done!")
                return

class Cloudformation:
    def __init__(self, cf_client):
        self.cf_client = cf_client

    def get_outputs(self, stack_name):
        stack = self.cf_client.describe_stacks(StackName=stack_name)["Stacks"][0]
        outputs = {}
        for o in stack["Outputs"]:
            outputs[o["OutputKey"]] = o["OutputValue"]
        return outputs

def main(args):
    session = boto3.session.Session(profile_name=args.profile)

    CLUSTER_NAME = "SatCompCluster"
    cf = Cloudformation(session.client("cloudformation"))
    stack_outputs = cf.get_outputs(f"job-queue-{args.project_name}")

    #print(stack_outputs)

    if args.cloud:
      output = subprocess.check_output(['./run-solver-main.sh', args.profile, CLUSTER_NAME, stack_outputs["SolverProjectDefinition"], stack_outputs["Subnet"], stack_outputs["SecurityGroupId"], args.file, str(int(args.NWorker)+1), args.project_name])
    else
      output = subprocess.check_output(['./run-solver-par.sh', args.profile, CLUSTER_NAME, stack_outputs["SolverProjectDefinition"], stack_outputs["Subnet"], stack_outputs["SecurityGroupId"], args.file, args.project_name])

    task_output = json.loads(output)
    print(task_output)
    task_arn = task_output['tasks'][0]['taskArn']
    task_id = task_arn.split('/')[2]

    main_task = Task(ecs_client=session.client("ecs"), cluster_name=CLUSTER_NAME, task_arn=task_arn)

    log_client = session.client("logs")
    log_analyzer = LogAnalyzer(log_client)
    ip_fetcher = IpFetch(log_analyzer)
    ip_addr = ip_fetcher.fetch_ip(args.project_name, task_id)

    for worker_Index in range(int(args.NWorker)):
        print("Creating "+str(worker_Index+1)+"...")
        workerOutput = subprocess.check_output(['./run-worker.sh', args.profile, CLUSTER_NAME, stack_outputs["SolverProjectDefinition"], stack_outputs["Subnet"], stack_outputs["SecurityGroupId"], args.file, str(int(args.NWorker)+1), ip_addr, str(worker_Index+1),args.project_name])

    print("Waiting for main task to complete...")
    main_task.wait_for_task_complete()

    logs = log_analyzer.fetch_logs(args.project_name, task_id)
    print(logs)

pars = argparse.ArgumentParser()
for arg in [{
        "flags": ["-p", "--profile"],
        "metavar": "P",
        "help": "What aws profile you will use",
        "required": True,
}, {
        "flags": ["-pn", "--project-name"],
        "help": "Project name",
        "metavar": "A",
        "required": True,
},{

    "flags": ["-f", "--file"],
    "metavar": "P",
    "help": "The file you are trying to solve",
    "required": True,
},
    {
        "flags": ["-c", "--cloud"],
        "metavar": "P",
        "help": "Whether this is a cloud job (True of False - default is True)",
        "required": False,
    },
{
    "flags": ["-N", "--NWorker"],
    "metavar": "N",
    "help": "Number of worker nodes",
    "required": True,
},
]:
    flags = arg.pop("flags")
    pars.add_argument(*flags, **arg)
if __name__=="__main__":
    args = pars.parse_args()
    main(args)
