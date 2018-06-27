---- MODULE MC ----
EXTENDS ShipsPassing, TLC

\* CONSTANT definitions @modelParameterConstants:0NUM_UPDATERS
const_1530140216126144000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530140216126145000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1530140216126146000 ==
EventualConsistency
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1530140216126147000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Wed Jun 27 15:56:56 PDT 2018 by dsmith
