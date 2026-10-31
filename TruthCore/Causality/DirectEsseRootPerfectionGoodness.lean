import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
import TruthCore.Case.Catholicism.CausalPerfectionTransfer
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1

/-! Conditional selected-root attributes, without a God predicate or naming.
InAct is a supplied global dictionary: correspondence to worlds and actual
perfections remains OPEN. Supreme goodness below is the existing causal
predicate, not moral perfection, omniscience or a divine identity. -/
namespace TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- All properties concern the SAME selected actual concrete root. Uniqueness
is among selected actual roots, not among all necessary individuals. -/
def PerfectRootAt {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R) (n : B) : Prop :=
  ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
    (∀ x, ActualRoot m w x → x = n) ∧ IsMaximumIn InAct MoreIn esse n ∧ IsPerfect InAct n

def NecessaryPerfectRootAt {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∃ n, PerfectRootAt m w InAct MoreIn esse n

def NecessaryPerfectSupremelyGoodRootAt {W B R : Type} (m : Profile W B) (w : W)
    (InAct GoodIn : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∃ n, PerfectRootAt m w InAct MoreIn esse n ∧
    IsSupremelyGood InAct GoodIn CausesIn esse n

/-- The pointwise q4 argument: esse universality reaches every distinct bearer;
preexistence transfers its actuality to this same supplied maximum. -/
theorem perfectOfMaximum {B R : Type} (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R) (n : B)
    (hMax : IsMaximumIn InAct MoreIn esse n)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hEM : ExcludedMiddle) : IsPerfect InAct n := by
  intro x r hx
  rcases hEM (x = n) with h | h
  · exact h ▸ hx
  · exact hPreexist n x r (hGenus n hMax x h (hBeing x r hx)) hx

/-- The pointwise q5/q6 application uses the EXISTING restricted transfer only
once the supplied maximum independently establishes universal esse causality. -/
theorem supremelyGoodOfMaximum {B R : Type} (InAct GoodIn : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R) (n : B)
    (hMax : IsMaximumIn InAct MoreIn esse n)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse) :
    IsSupremelyGood InAct GoodIn CausesIn esse n := by
  have hAll := hGenus n hMax
  refine ⟨(hGoodness n esse).mpr hMax.1, ?_⟩
  intro x r hOther hx
  exact hTransfer n hAll x r hOther (hAll x hOther (hBeing x r hx)) hx
end TruthCore.Causality.DirectEsseRootPerfectionGoodness
