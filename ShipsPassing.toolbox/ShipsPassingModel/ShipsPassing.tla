---------------------------- MODULE ShipsPassing ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NUM_UPDATERS


(* --algorithm concurrentModification

\*vals is a map of updater id to current value, initialized to 0
variables vals  = [val \in 1..NUM_UPDATERS |-> 0];

\* Each updater will update it's current value to it's id
\* And then update everyone else it it's id
fair process updater \in 1..NUM_UPDATERS
variable other=1;
begin
  \* Update our value to self
  UPDATE_SELF: 
    vals[self] := self;
  \*Update everyone else's value.
  UPDATE_OTHERS: while other <= NUM_UPDATERS do
    if other = self then
      skip;
    else
      vals[other] := self
    end if;
    other := other + 1;
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES vals, pc, other

vars == << vals, pc, other >>

ProcSet == (1..NUM_UPDATERS)

Init == (* Global variables *)
        /\ vals = [val \in 1..NUM_UPDATERS |-> 0]
        (* Process updater *)
        /\ other = [self \in 1..NUM_UPDATERS |-> 1]
        /\ pc = [self \in ProcSet |-> "UPDATE_SELF"]

UPDATE_SELF(self) == /\ pc[self] = "UPDATE_SELF"
                     /\ vals' = [vals EXCEPT ![self] = self]
                     /\ pc' = [pc EXCEPT ![self] = "UPDATE_OTHERS"]
                     /\ other' = other

UPDATE_OTHERS(self) == /\ pc[self] = "UPDATE_OTHERS"
                       /\ IF other[self] <= NUM_UPDATERS
                             THEN /\ IF other[self] = self
                                        THEN /\ TRUE
                                             /\ vals' = vals
                                        ELSE /\ vals' = [vals EXCEPT ![other[self]] = self]
                                  /\ other' = [other EXCEPT ![self] = other[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "UPDATE_OTHERS"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << vals, other >>

updater(self) == UPDATE_SELF(self) \/ UPDATE_OTHERS(self)

Next == (\E self \in 1..NUM_UPDATERS: updater(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NUM_UPDATERS : WF_vars(updater(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

EventualConsistency == <>[](\A x \in 1..NUM_UPDATERS : vals[x] = vals[1])
=============================================================================


