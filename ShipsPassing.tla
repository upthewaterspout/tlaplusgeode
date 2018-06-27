---------------------------- MODULE ShipsPassing ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NUM_UPDATERS

OtherUpdaters(updater) == {x \in 1..NUM_UPDATERS : x /= updater}

(* --algorithm concurrentModification

\*vals is a map of updater id to current value, initialized to 0
variables vals  = [val \in 1..NUM_UPDATERS |-> 0] ;

\* Each updater will update it's current value to it's id
\* And then update everyone else it it's id
fair process updater \in 1..NUM_UPDATERS
begin
  \* Update our value to self
  UPDATE_SELF: 
    vals[self] := self;
  \*Update everyone else's value. Hmm, this should not be atomic but TLA+ wants me to 
  \* Put the label outside the with
  UPDATE_OTHERS:
  with other \in OtherUpdaters(self) do
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
        /\ pc = [self \in ProcSet |-> "UPDATE_SELF"]

UPDATE_SELF(self) == /\ pc[self] = "UPDATE_SELF"
                     /\ vals' = [vals EXCEPT ![self] = self]
                     /\ pc' = [pc EXCEPT ![self] = "UPDATE_OTHERS"]

UPDATE_OTHERS(self) == /\ pc[self] = "UPDATE_OTHERS"
                       /\ \E other \in OtherUpdaters(self):
                            vals' = [vals EXCEPT ![other] = self]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]

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


