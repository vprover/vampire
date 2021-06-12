#!/bin/bash
/usr/sbin/sshd -D &

# arg1 is ip address and arg2 is problem path
./vampire --mode smtcomp --ignore_missing on --cores 0 $1
