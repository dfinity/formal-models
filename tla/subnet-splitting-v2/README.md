# A high-level TLA+ model of subnet splitting v2

The main file is `Subnet_Splitting_v2.tla`. For easier readability and potential reusability, we split the model into several modules: one for the induction rules, one for message execution, one for upgrading the local registry. 

Additionally, the `ScenarioX.tla` models define the individual scenarios for model checking. The scenarios involve two canisters with different topologies:
1. One moved to the child subnet and one on another unrelated subnet.
1. One staying on the parent subnet and one moving to the child subnet.
1. Both moving to the child subnet.
1. Both moving to the child subnet with one created during the move

There are also two configurations:
1. `Splitting_Safety.cfg` - checks that no assertions are thrown (e.g., due to dropping messages) and that no request reordering happens. Also contains a bunch of sanity tests that can be enabled to get some confidence that the model isn't flawed. You can also run this with a deadlock check on to check for deadlocks.
1. `Splitting_Liveness.cfg` - checks whether every requests eventually receives a response. This should hopefully be implied by the safety check, but it's there for the peace of mind. Liveness checks are generally a lot slower.

You can use the `test-all-scenarios.sh` to all the scenarios 
```
$ test-all-scenarios.sh <config_file> <log_file>
```  