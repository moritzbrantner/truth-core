module

public import TruthCore.Explanation.JointCooperation

/-! Matched response experiment after #735/#744 (#953).

The two Exercises share the Bool-pair scenario carrier, the actual all-on
scenario, and the public occurrence table of inputs a,b and target t/2.
Their *hidden* event/bearer carriers and causal group records are distinct.
Even complete scenario sufficiency of every record does not identify the
number of graph foundations. The scenarios are NOT asserted to be possible
worlds or genuine causal interventions; their productive interpretation is
still an independent philosophical question. -/

@[expose] public section

namespace TruthCore.Explanation.CompleteResponseParity

open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Explanation.JointCooperation

/-- Repair #744's single-source control by making the root's occurrence
contingent on both scenario inputs. Unlike `single`, the two records from
the root to a,b can then be jointly sufficient in every supplied scenario.
This changes no group or actual-world occurrence and introduces no bearer. -/
def completedSingle : Exercise Unit SingleEvent SingleGroup (Bool × Bool) :=
  { single with occurs := fun s e => match e with
      | .r => s.1 = true ∧ s.2 = true
      | .a => s.1 = true
      | .b => s.2 = true
      | .t => s.1 = true ∧ s.2 = true }

/-- One shared observation interface, NOT an identification of their hidden
event carriers: equal input and effect truth tables at all four scenarios. -/
def MatchedObservations : Prop :=
  ∀ s : Bool × Bool,
    (completedSingle.occurs s .a ↔ exercisePlural.occurs s 0) ∧
    (completedSingle.occurs s .b ↔ exercisePlural.occurs s 1) ∧
    (completedSingle.occurs s .t ↔ exercisePlural.occurs s 2)

/-- Unlike the original single-source fixture, BOTH comparison structures
are coherent and every record is jointly sufficient for all allowed scenarios. -/
def CompleteProfiles : Prop :=
  (completedSingle.coherent ∧ ∀ g, completedSingle.jointlySufficient g) ∧
  (exercisePlural.coherent ∧ ∀ g, exercisePlural.jointlySufficient g)

/-- A least graph source exists in the strengthened single case, but not in
the same-observations plural case; these are separate graph interpretations. -/
def RootParity : Prop :=
  least completedSingle.exercisedGroups.graph .r ∧
  ¬ (∃ s, least exercisePlural.exercisedGroups.graph s)

/-- In each model both target contributors are indispensable in its supplied
scenario space, but only the strengthened single model has a common source
that scenario-suffices for both. This does not certify *production*. -/
def CooperationParity : Prop :=
  Needed completedSingle .ab .a .b ∧
  Needed exercisePlural 0 0 1 ∧
  CommonSource completedSingle .a .b ∧
  ¬ CommonSource exercisePlural 0 1

/-- Both groups admit full inductive `Supply`, still only the proposed #734
standard, not actual existential support or explanatory adequacy. -/
def SupplyParity : Prop :=
  (∀ e, Supply completedSingle.groups singleIntrinsic e) ∧
  (∀ e, Supply exercisePlural.groups (TruthCore.Explanation.UltimateAdequacy.intrinsic .plural) e)

/-- The original one-source example fails the stronger all-record-sufficiency
test. Without that control the new comparison would just repeat #744. -/
def OriginalGap : Prop := ¬ single.jointlySufficient .ra

def Certificate : Prop :=
  MatchedObservations ∧ CompleteProfiles ∧ RootParity ∧ CooperationParity ∧
  SupplyParity ∧ OriginalGap

end TruthCore.Explanation.CompleteResponseParity
