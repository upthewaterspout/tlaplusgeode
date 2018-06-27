---- MODULE MC ----
EXTENDS ConcurrencyChecksShipsPassing, TLC

\* CONSTANT definitions @modelParameterConstants:0NUM_UPDATERS
const_1530140230756148000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530140230756149000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1530140230756150000 ==
Termination
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1530140230756151000 ==
EventualConsistency
----
=============================================================================
\* Modification History
\* Created Wed Jun 27 15:57:10 PDT 2018 by dsmith
