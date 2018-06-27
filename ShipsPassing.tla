---------------------------- MODULE ShipsPassing ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NUM_UPDATERS
(* --algorithm concurrentModification

\*vals is a map of updater id to current value, initialized to 0
variables vals  = [val \in 1..NUM_UPDATERS |-> 0] 


\*define
\* Other updaters is the set of updater ids that doesn't include the given updater
\*OtherUpdaters(updater) == {x \in 1..NUM_UPDATERS : x \= updater}
\*end define

\* Each updater will update it's current value to it's id
\* And then update everyone else it it's id
process updater \in 1..NUM_UPDATERS
begin
  \* Update our value to self
  A: 
    vals[self] := self;
  \*Update everyone else's value. Hmm, this should not be atomic but TLA+ wants me to 
  \* Put the label outside the with
  B:
  with other \in 1..NUM_UPDATERS do
    vals[other] := self;
  end with;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES vals, pc

vars == << vals, pc >>

ProcSet == (1..NUM_UPDATERS)

Init == (* Global variables *)
        /\ vals = [val \in 1..NUM_UPDATERS |-> 0]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ vals' = [vals EXCEPT ![self] = self]
           /\ pc' = [pc EXCEPT ![self] = "B"]

B(self) == /\ pc[self] = "B"
           /\ \E other \in 1..NUM_UPDATERS:
                vals' = [vals EXCEPT ![other] = self]
           /\ pc' = [pc EXCEPT ![self] = "Done"]

updater(self) == A(self) \/ B(self)

Next == (\E self \in 1..NUM_UPDATERS: updater(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================

