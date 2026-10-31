import TruthCore.Causality.NecessarySimplePlurality
import TruthCore.Causality.WholeRosterFoundation
import TruthCore.Causality.DirectEsseRootRoute
import TruthCore.Causality.NecessaryRootUniqueness

/-! Exact-interface extension of the ORIGINAL four-being #681 interpretation.
No existing carrier, world, existence, act, cause, power-support, composition,
essence or esse field changes. The later five-being PartFreePlurality control
is NOT substituted for it. This is a finite formal control, not metaphysical
possibility or a complete explanation of the selected actual being.
-/
namespace TruthCore.Causality.DirectEsseGenusOmissionControl
open TruthCore.Causality.NecessarySimplePlurality
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessaryRootUniqueness (UniqueNecessaryActualRootAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A VIEW of the old Ontic and its existing direct esse-support relation.
All four original candidates are stipulated concrete. This matches the encoded
interface, not an independent warrant identifying represented support with real
existential grounding. No new world/individual carrier or causal law is added. -/
def profile : TruthCore.Causality.BruteFoundationBoundary.Profile Bool Being where
  ontic := ontic
  concrete := fun _ => True
  grounds := power.supportsEsse

/-- Newly supplied grading dictionary on the SAME old carrier. A higher grade
means a strictly smaller OLD rank, with both bearers in act in that SAME respect.
The original model had no MoreIn assignment; no old grading theorem is silently
reinterpreted. This assignment asserts no metaphysical priority/degree identity. -/
def moreIn (r : Respect) (y x : Being) : Prop :=
  inAct y r ∧ inAct x r ∧ component y x

/-- Exactly the six nonlogical retained interfaces of the eight-input direct
root-uniqueness theorem when genus causality I is withheld. Explicit EM remains
the result's input, so together they satisfy ALL seven remaining inputs. -/
def RetainedInputs : Prop :=
  InhabitedConcreteAt profile.ontic profile.concrete false ∧
  WholeRosterNotTrapped profile false ∧
  EveryContingentGroundedAt profile false ∧
  ExistingInActAt profile.ontic inAct Respect.esse false ∧
  EsseCauseIsActualConcreteGround profile false esseProfile.CausesIn Respect.esse ∧
  GradesByApproachToAMaximumReading inAct moreIn

/-- Preserve the original joint certificate, expose a positive esse grade and
tied weak esse maxima, and retain two distinct ACTUAL SELECTED roots. The imported
uniqueness theorem then excludes genus causality in this exact assignment.
The original model's all-present ontology makes contingent dependence vacuous;
no contingent effect or q3a8 part-freeness is claimed. This is NOT at-most-one
God, uniqueness of every necessary individual, or an adequate worldview. -/
def Control : Prop :=
  JointControl ∧ RetainedInputs ∧
  moreIn Respect.esse Being.left Being.instrument ∧
  IsMaximumIn inAct moreIn Respect.esse Being.left ∧
  IsMaximumIn inAct moreIn Respect.esse Being.right ∧
  ActualRoot profile false Being.left ∧ ActualRoot profile false Being.right ∧
  Being.left ≠ Being.right ∧
  ¬ UniqueNecessaryActualRootAt profile false ∧
  ¬ MaximumInGenusCausesAllInGenusReading inAct moreIn esseProfile.CausesIn

end TruthCore.Causality.DirectEsseGenusOmissionControl
