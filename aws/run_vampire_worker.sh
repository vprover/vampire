#!/bin/bash

# arg1 is ip address and arg2 is problem path
vampire/build/bin/vampire --mode smtcomp --ignore_missing on --cores 0 -si on -rs on $2
