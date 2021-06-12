#!/usr/bin/env python3
from os import listdir
from os.path import isfile, join

HOST_FILE_PATH="/tmp/"
external_ips = []
onlyfiles = [f for f in listdir(HOST_FILE_PATH) if isfile(join(HOST_FILE_PATH, f))]
combined_text = ""

for filename in onlyfiles:
    if "hostfile" in filename:
        with open(join(HOST_FILE_PATH, filename)) as f:
            combined_text+=f.read()
with open("combined_hostfile", "w") as f:
    f.write(combined_text)
