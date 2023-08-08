#!/bin/sh

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
mkdir .vscode
cat <<EOF > .vscode/settings.json
{
    "git.ignoreLimitWarning": true,
    "tlaplus.java.options": "-cp $DIR/tlatools/CommunityModules.jar:$DIR/tlatools//CommunityModules-deps.jar:$DIR/tlatools/tla2tools.jar"
}
EOF
