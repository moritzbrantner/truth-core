import TruthCore.Causality.DirectEsseRootPerfectionGoodness

/-! Full-background omission control on the EXACT #732 secondary-only rival.
Only an all-present/all-concrete Profile view is added; the old role carrier,
act, grades and causal responsibility fields are unchanged. Formal compatibility
is not metaphysical possibility, morality or an adequate explanation. -/
namespace TruthCore.Causality.DirectEsseRootGoodnessOmission
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- New modal/ground view of the OLD secondary-only causal dictionary.
Existence and concreteness are stipulated universally; grounds at esse use the
same OLD transferCause false. No change to any original role or dictionary. -/
def model : Profile Bool TransferRole where
  ontic := { frame := ⟨fun _ _ => True⟩
             ExistsAt := fun _ _ => True
             Causes := fun _ c x => transferCause false c x false }
  concrete := fun _ => True
  grounds := fun _ c x => transferCause false c x false

/-- Ten nonlogical inputs other than the restricted transfer premise. Supplied
EM makes the exact eleven remaining inputs of the twelve-input goodness route.
The full old global genus/background remains separately retained in Control. -/
def RetainedInputs : Prop :=
  InhabitedConcreteAt model.ontic model.concrete false ∧
  WholeRosterNotTrapped model false ∧ EveryContingentGroundedAt model false ∧
  MaximumInBeingCausesAllBeingsReading transferAct (transferMore false) (transferCause false) false ∧
  ExistingInActAt model.ontic transferAct false false ∧
  EsseCauseIsActualConcreteGround model false (transferCause false) false ∧
  GradesToMaximumAtBeing transferAct (transferMore false) false ∧
  ActualityOnlyInsofarAsBeingReading transferAct false ∧
  PerfectionsOfEffectPreexistInCauseReading transferAct (transferCause false) false ∧
  GoodnessIsActualityReading transferAct transferAct

/-- Same selected source is actual, necessary, the unique selected root, maximal
in esse and perfect. It is good in esse but does not cause the recipient's skill,
so the existing causal supreme-goodness predicate and whole endpoint fail.
No necessary-person, moral-goodness, God or reality correspondence is asserted. -/
def Control : Prop :=
  SecondaryOnlyTransferSurvives ∧ RetainedInputs ∧
  PerfectRootAt model false transferAct (transferMore false) false .source ∧
  transferAct .source false ∧
  ¬ IsSupremelyGood transferAct transferAct (transferCause false) false .source ∧
  ¬ NecessaryPerfectSupremelyGoodRootAt model false transferAct transferAct
    (transferMore false) (transferCause false) false
end TruthCore.Causality.DirectEsseRootGoodnessOmission
