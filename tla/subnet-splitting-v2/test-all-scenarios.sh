#!/bin/bash

usage () {
    cat <<EOM
    usage: $(basename $0) <tlc_config_file> <log_file>
EOM
    exit 1
}

[ $# -ne 2 ] && { usage; }


CONFIG_FILE=$1
LOG_FILE=$2
SCENARIOS=`ls Scenario?.tla`

for scenario in $SCENARIOS
do
    ../run-tlc.sh $scenario $CONFIG_FILE >> $LOG_FILE
done