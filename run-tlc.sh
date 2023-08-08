#!/bin/sh

usage () {
    cat <<EOM
    usage: $(basename $0) <tla_model_file> <tlc_config_file>
EOM
    exit 1
}

SCRIPT=$(readlink -f "$0")
# Absolute path this script is in, thus /home/user/bin
SCRIPTPATH=$(dirname "$SCRIPT")

[ $# -ne 2 ] && { usage; }

java -cp $SCRIPTPATH/tlatools/CommunityModules-deps.jar:$SCRIPTPATH/tlatools/tla2tools.jar -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -XX:+UseParallelGC -Xmx200G tlc2.TLC $1 -modelcheck -config $2 -workers 54 -checkpoint 0 -difftrace -lncheck final

