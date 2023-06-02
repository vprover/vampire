#!/bin/bash

echo "Running in parallel mode on problem path $1"

# Just run vampire
/competition/vampire --mode smtcomp --ignore_missing on --bad_option off --cores 0 -t 0 $1

