#!/usr/bin/env bash

echo "This is the command I've been using for testing"

# This test uses our own S3 bucket called smtcomp-problems-for-testing

python3 run_example.py --profile vampire --project-name vampire -f x2015_09_10_16_59_44_027_1051487.smt_in.smt2 --cloud False

#python3 run_example.py --profile vampire --project-name vampire -f non-incremental/UF/20170428-Barrett/cdt-cade2015/nada/afp/abstract_completeness/x2015_09_10_16_59_44_027_1051487.smt_in.smt2 --cloud False

