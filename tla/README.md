# TLA+ Models of the IC

This directory includes TLA+ models of different Internet Computer (IC) components. Many of the models model canisters (IC smart contracts), but some model other aspects of the platform (e.g, subnet splitting, or a basic model of the consensus algorithm).

The modules use TLA community modules (the TLA+ "stdlib"):
https://github.com/tlaplus/CommunityModules

If you're using VSCode, you can set up the required community modules paths using `init-vscode.sh`, or do it manually by following the instructions here:
https://github.com/tlaplus/vscode-tlaplus/issues/249

To analyze a model from the command line, invoke the `run-tlc.sh` script.
You can edit it to control the memory limits and the number of worker threads,

