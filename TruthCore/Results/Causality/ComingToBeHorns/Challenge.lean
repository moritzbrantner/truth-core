import TruthCore.Causality.ComingToBeHorns
import TruthCore.Results.Causality.ContingentComingToBe.Solution
import TruthCore.Results.Causality.IndexedSignalReaper.Solution
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Finset.Nat

namespace TruthCore.Results.Causality.ComingToBeHorns
open TruthCore.Causality.ComingToBeHorns
open TruthCore.Causality.ContingentComingToBe
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.TemporalHistory (History)
open TruthCore.Case.Catholicism.StageOne.CausalFinitism (FiniteDistinctAncestry)

/-- Horn H2 priced by the Grim Reaper results. Under the Reaper assembly
bridge, every populated moment of every accessible history has a founded past:
otherwise an endless descent below it would carry stations satisfying the four
local rules, which `IndexedSignalReaper.impossible` refutes. -/
theorem populatedPastsFoundedOfReaper {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (w : W)
    (hAssembly : ReaperAssembly h Concrete w) :
    PopulatedPastsFounded h Concrete w := by
  sorry

/-- Horn H2 priced by causal finitism. If the momentary states of each
accessible history have finitely many causal ancestors, and every earlier
state is a causal ancestor of the state at a populated moment, every populated
moment has a founded past: an endless descent below it would give infinitely
many distinct ancestors. No-loops is not needed: the strict temporal order
already makes the descending moments distinct. -/
theorem populatedPastsFoundedOfStateFinitism {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (stateCause : W → T → T → Prop)
    (w : W)
    (hFinite : StateCausalFinitism h stateCause w)
    (hBridge : PrecedenceIsStateCausation h Concrete stateCause w) :
    PopulatedPastsFounded h Concrete w := by
  sorry

/-- Premise A3′ of the modal spine from founded populated pasts and the
possibility of a populated history whose contingent concrete things all have
earlier-present concrete grounds. -/
theorem possiblyFoundedOfEarlierGrounds {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (grounds : W → B → B → Prop) (w : W)
    (hPast : PopulatedPastsFounded h Concrete w)
    (hPossible : PossiblyEarlierGroundedPopulated h Concrete grounds w) :
    PossiblyFoundedComingToBe h Concrete w := by
  sorry

open TruthCore.Causality.ComingToBeHorns.Control
open TruthCore.Causality.ContingentComingToBe.Control (endless)
open TruthCore.Causality.InertEmptiness.Control (all rooted)

/-- Omission and nonvacuity controls. -/
theorem controls : TruthCore.Causality.ComingToBeHorns.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ComingToBeHorns
