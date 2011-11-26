#!/bin/bash

VAMP_EXEC="./vampire_rel"
CL_CMD="$VAMP_EXEC --mode clausify"
CL_REST_CMD="$VAMP_EXEC --mode clausify --epr_preserving_skolemization on --epr_preserving_naming on --epr_restoring_inlining on"
PROFILE_CMD="$VAMP_EXEC --mode profile"

for F in $*; do
        if $CL_CMD $F | $PROFILE_CMD | grep -q "EPR"; then
                continue
        fi
        if $CL_REST_CMD $F | $PROFILE_CMD | grep -q "EPR"; then
                echo $F
        fi
done