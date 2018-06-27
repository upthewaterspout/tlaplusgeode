---------------------------- MODULE ConcurrencyChecksShipsPassing ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NUM_UPDATERS

shouldUpdate(newVal, oldVal) == IF newVal[3] = oldVal[3]
                                 THEN newVal[2] >= oldVal[2]
                                 ELSE newVal[3] >= oldVal[3]

(* --algorithm concurrentModification

\*vals is a structure of updater id to a tuple of <<current_value, last_updater, version>>
variables vals  = [val \in 1..NUM_UPDATERS |-> <<0,val,0>>] ;

\* Each updater will update it's current value to it's id
\* And then update everyone else it it's id
fair process updater \in 1..NUM_UPDATERS
variables new_value = <<0,0,0>>, other=1;
begin
  SET_NEW_VALUE:
    new_value := <<self,self,vals[self][3]+1>>;
  \* Update our value to self
    vals[self] := IF shouldUpdate(new_value, vals[self])
      THEN new_value
      ELSE vals[self];
      
  \*Update everyone else's value.
  UPDATE_OTHERS: while other <= NUM_UPDATERS do
    if other = self then
      skip;
    else
      vals[other] := IF shouldUpdate(new_value, vals[other])
      THEN new_value
      ELSE vals[other];
    end if;
    other := other + 1;
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES vals, pc, new_value, other

vars == << vals, pc, new_value, other >>

ProcSet == (1..NUM_UPDATERS)

Init == (* Global variables *)
        /\ vals = [val \in 1..NUM_UPDATERS |-> <<0,val,0>>]
        (* Process updater *)
        /\ new_value = [self \in 1..NUM_UPDATERS |-> <<0,0,0>>]
        /\ other = [self \in 1..NUM_UPDATERS |-> 1]
        /\ pc = [self \in ProcSet |-> "SET_NEW_VALUE"]

SET_NEW_VALUE(self) == /\ pc[self] = "SET_NEW_VALUE"
                       /\ new_value' = [new_value EXCEPT ![self] = <<self,self,vals[self][3]+1>>]
                       /\ vals' = [vals EXCEPT ![self] =             IF shouldUpdate(new_value'[self], vals[self])
                                                         THEN new_value'[self]
                                                         ELSE vals[self]]
                       /\ pc' = [pc EXCEPT ![self] = "UPDATE_OTHERS"]
                       /\ other' = other

UPDATE_OTHERS(self) == /\ pc[self] = "UPDATE_OTHERS"
                       /\ IF other[self] <= NUM_UPDATERS
                             THEN /\ IF other[self] = self
                                        THEN /\ TRUE
                                             /\ vals' = vals
                                        ELSE /\ vals' = [vals EXCEPT ![other[self]] =                IF shouldUpdate(new_value[self], vals[other[self]])
                                                                                      THEN new_value[self]
                                                                                      ELSE vals[other[self]]]
                                  /\ other' = [other EXCEPT ![self] = other[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "UPDATE_OTHERS"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << vals, other >>
                       /\ UNCHANGED new_value

updater(self) == SET_NEW_VALUE(self) \/ UPDATE_OTHERS(self)

Next == (\E self \in 1..NUM_UPDATERS: updater(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NUM_UPDATERS : WF_vars(updater(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

EventualConsistency == <>[](\A x \in 1..NUM_UPDATERS : vals[x] = vals[1])
=============================================================================


