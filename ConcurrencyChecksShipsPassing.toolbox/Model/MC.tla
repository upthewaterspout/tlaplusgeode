---- MODULE MC ----
EXTENDS ConcurrencyChecksShipsPassing, TLC

\* CONSTANT definitions @modelParameterConstants:0NUM_UPDATERS
const_1530143515843171000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530143515843172000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1530143515843173000 ==
Termination
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1530143515843174000 ==
EventualConsistency
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1530143515843175000 ==
IfAnyoneIsLastTheyWin
----
=============================================================================
\* Modification History
\* Created Wed Jun 27 16:51:55 PDT 2018 by dsmith
