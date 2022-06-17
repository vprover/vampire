#!/bin/bash

# arg1 is ip address and arg2 is problem path

IFS=. read -r a b c d <<< "$1"
rand="$((a * 256 ** 3 + b * 256 ** 2 + c * 256 + d))"
echo "Using random number $rand"

vampire/build/bin/vampire --mode smtcomp --ignore_missing on --cores 0 -si on -rs on --random_seed $rand $2
