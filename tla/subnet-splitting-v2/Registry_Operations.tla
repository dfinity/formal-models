---- MODULE Registry_Operations ----
EXTENDS TLC, Common, Integers, Functions

\* @type: ($registries, Int, $subnets, $subnetId) => $subnets;
Apply_Registry_Update(registries, registry_version, s, subnet_id) ==
  LET
    reg == registries[registry_version]
    old_reg == registries[registry_version - 1]
    rt == reg.routing_table
    \* TODO: we should probably only allow this if the subnet is unhalted,
    \* but we'd need to make Split_State more fine-grained for this to work
    \* (as we rely on applying the registry update on the parent in order to trim
    \* the state of the existing canisters)
    state == s[subnet_id]
    canisters_to_remove == { c \in DOMAIN state.canister: /\ ~Hosted(rt, c, subnet_id)  }
    canisters_to_spin_off == { c \in DOMAIN rt : rt[c].migration_list # <<>> /\ rt[c].migration_list[1] = subnet_id }
    newly_discovered_subnets == DOMAIN reg.subnet_info \ DOMAIN old_reg.subnet_info
    subnet_ids_to_spin_off == { rt[c].migration_list[2] : c \in canisters_to_spin_off }
    checks ==  
        /\ Assert(canisters_to_remove = canisters_to_spin_off, "Newly non-hosted canisters not the same as canisters to spin out")
    new_self_state == [ s[subnet_id] EXCEPT
            !.registry_version = registry_version, 
            !.canister = Remove_Arguments(@, canisters_to_remove),
            !.incoming_index = [ sid \in newly_discovered_subnets |-> 0 ] @@ @,
            !.outgoing_index = [ sid \in newly_discovered_subnets |-> 0 ] @@ @
        ]
  IN
    IF subnet_ids_to_spin_off # {} THEN
        LET
            child_subnet_id == CHOOSE id \in subnet_ids_to_spin_off: TRUE
            more_checks == 
                Assert(subnet_ids_to_spin_off = { child_subnet_id }, "Asked to spin off multiple subnet IDs")
        IN 
            child_subnet_id :> [
                registry_version |-> registry_version,
                canister |-> Restrict(s[subnet_id].canister, canisters_to_spin_off),
                incoming_index |-> [ sid \in DOMAIN reg.subnet_info |-> 0 ],
                outgoing_index |-> [ sid \in DOMAIN reg.subnet_info |-> 0 ]
            ] @@ [ s EXCEPT ![subnet_id] = new_self_state ]
    ELSE [ s EXCEPT ![subnet_id] = new_self_state ]

\* "Spontaneous" event: update a subnet's local view on the registry (i.e., fetch new registry versions)
Update_Local_Registry(subnet_id) ==
  /\ subnet_id \in DOMAIN subnet
  /\ LET
      s == subnet[subnet_id]
    IN
      /\ \E new_version \in s.registry_version + 1..Len(registry):
          /\ subnet' = Apply_Registry_Update(registry, new_version, subnet, subnet_id)
      /\ UNCHANGED << stream, registry  >>



====