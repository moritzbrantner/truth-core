import TruthCore.Metaethics.NaturalisticRealism

/-! #249: theory bundles for the selected naturalist fragments. Source-level
answers and strongest replies, shared questions and exact counts are recorded
in docs/naturalistic-moral-realism.md. Model consistency does not establish
the existence of the proposed natural grounds or their normative adequacy. -/
namespace TruthCore.Comparison.NaturalisticRealism
open TruthCore.Metaethics.NaturalisticRealism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Railton's welfare and impartial-rightness identifications, cognitive
truth-aptness and descriptive rightness ascriptions. -/
def Railton (s : Sig) : Prop :=
  TruthCore.English.Railton.WelfareReading s.GoodFor s.SatisfiesObjectiveInterest ∧
  TruthCore.English.Railton.RightnessReading s.Right s.ImpartialCriterion ∧
  MoralJudgmentsAreTruthAptReading s.base.Moral s.base.TruthApt ∧
  DescriptiveTruth s.Ascribes s.base.Holds s.Right

/-- Boyd's positive homeostatic-goodness fragment, truth-aptness and
ascriptions of that goodness. No forced verdict on vague cases is included. -/
def Boyd (s : Sig) : Prop :=
  TruthCore.English.Boyd.ClusterGoodnessReading s.base.GoodAct s.FostersGoods s.SustainsMechanisms ∧
  MoralJudgmentsAreTruthAptReading s.base.Moral s.base.TruthApt ∧
  DescriptiveTruth s.Ascribes s.base.Holds s.base.GoodAct

/-- Nonvacuous model with true and false moral ascriptions, actual cognitive
error, and a right act for which an agent has no instrumental reason. -/
def RailtonConsistent : Prop :=
  ∃ s : Sig, Railton s ∧ ErrorOccurs s ∧ RightWithoutUniversalReasons s ∧
    TrueMoralAscriptionOccurs s

/-- The same test for Boyd's distinct positive-goodness fragment. -/
def BoydConsistent : Prop :=
  ∃ s : Sig, Boyd s ∧ ErrorOccurs s ∧ GoodWithoutUniversalReasons s ∧
    TrueMoralAscriptionOccurs s

end TruthCore.Comparison.NaturalisticRealism
