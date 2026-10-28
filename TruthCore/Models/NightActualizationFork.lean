import TruthCore.Models.NightCosmogony
import TruthCore.Alternatives.NightActualizationFork

/-! Joint finite witnesses for the Night actualization fork. The four original
Night models are reused unchanged. Each closed certificate concerns one model;
no separate interpretations are combined. `Overlap` shows that the self-mover
and distinct-mover horns can hold for the same unpreceded moved potency.
`NonactualMover` distinguishes lacking an actual mover from lacking any mover.
These are satisfiability witnesses of the encoding, not metaphysical claims. -/
namespace TruthCore.Models.NightActualizationFork

open TruthCore.Models.FiniteSupport
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.NightCosmogony
open TruthCore.Alternatives.NightActualizationFork

namespace NoReduction
abbrev model := TruthCore.Models.NightCosmogony.NoReduction.model

theorem fork : NightActualizationFork model.InAct model.InPotency model.MovedIn
    model.MovesIn model.PriorSimply := by decide

theorem noActualMover : NoActualMoverAt model.InAct model.MovesIn false () := by decide

theorem noMover : ¬ ∃ y, model.MovesIn y false () := by decide

theorem violatesMover : ¬ ReducedOnlyByAMoverReading model.MovedIn model.MovesIn := by decide

theorem actual : MovesOnlyAsInActReading model.MovesIn model.InAct := by decide

theorem notBoth : NotActAndPotencyInSameRespectReading model.InAct model.InPotency := by decide

theorem noForcedBranch : ¬ NightNonpriorOtherActualMover model.InAct model.InPotency
    model.MovedIn model.MovesIn model.PriorSimply := by decide
end NoReduction

namespace SelfMover
abbrev model := TruthCore.Models.NightCosmogony.SelfMover.model

theorem fork : NightActualizationFork model.InAct model.InPotency model.MovedIn
    model.MovesIn model.PriorSimply := by decide

theorem actualSelfMover : ActualSelfMoverAt model.InAct model.MovesIn false () := by decide

theorem noOtherActualMover :
    ¬ NonpriorOtherActualMoverAt model.InAct model.MovesIn model.PriorSimply false () := by decide

theorem mover : ReducedOnlyByAMoverReading model.MovedIn model.MovesIn := by decide

theorem actual : MovesOnlyAsInActReading model.MovesIn model.InAct := by decide

theorem violatesNotBoth :
    ¬ NotActAndPotencyInSameRespectReading model.InAct model.InPotency := by decide

theorem noForcedBranch : ¬ NightNonpriorOtherActualMover model.InAct model.InPotency
    model.MovedIn model.MovesIn model.PriorSimply := by decide
end SelfMover

namespace Residual
abbrev model := TruthCore.Models.NightCosmogony.Residual.model

theorem mover : ReducedOnlyByAMoverReading model.MovedIn model.MovesIn := by decide

theorem actual : MovesOnlyAsInActReading model.MovesIn model.InAct := by decide

theorem notBoth : NotActAndPotencyInSameRespectReading model.InAct model.InPotency := by decide

theorem noFork : ¬ NightActualizationFork model.InAct model.InPotency model.MovedIn
    model.MovesIn model.PriorSimply := by decide

theorem noForcedBranch : ¬ NightNonpriorOtherActualMover model.InAct model.InPotency
    model.MovedIn model.MovesIn model.PriorSimply := by decide
end Residual

namespace OtherMover
abbrev model := TruthCore.Models.NightCosmogony.OtherMover.model

theorem fork : NightActualizationFork model.InAct model.InPotency model.MovedIn
    model.MovesIn model.PriorSimply := by decide

theorem forcedBranch : NightNonpriorOtherActualMover model.InAct model.InPotency
    model.MovedIn model.MovesIn model.PriorSimply := by decide

theorem mover : ReducedOnlyByAMoverReading model.MovedIn model.MovesIn := by decide

theorem actual : MovesOnlyAsInActReading model.MovesIn model.InAct := by decide

theorem notBoth : NotActAndPotencyInSameRespectReading model.InAct model.InPotency := by decide

theorem noSelfMover : ¬ ActualSelfMoverAt model.InAct model.MovesIn false () := by decide

/-- One model jointly satisfies the Night background and all three root
premises used to force the distinct nonprior actual-mover horn. -/
theorem jointRootBackground :
    UnprecededPotencyActualizedReading model.InAct model.InPotency model.MovedIn model.PriorSimply ∧
    ReducedOnlyByAMoverReading model.MovedIn model.MovesIn ∧
    MovesOnlyAsInActReading model.MovesIn model.InAct ∧
    NotActAndPotencyInSameRespectReading model.InAct model.InPotency := by decide
end OtherMover

namespace Overlap
def model : TruthCore.Models.NightCosmogony.Model where
  InAct := fun _ _ => True
  InPotency := fun x _ => x = false
  MovedIn := fun x _ => x = false
  MovesIn := fun _ x _ => x = false
  PriorSimply := fun _ _ => False

theorem background : UnprecededPotencyActualizedReading model.InAct model.InPotency
    model.MovedIn model.PriorSimply := by decide

theorem fork : NightActualizationFork model.InAct model.InPotency model.MovedIn
    model.MovesIn model.PriorSimply := by decide

theorem forcedBranch : NightNonpriorOtherActualMover model.InAct model.InPotency
    model.MovedIn model.MovesIn model.PriorSimply := by decide

/-- The very same selected potency has both an actual self-mover and a
distinct actual mover without simple priority. Coverage is not exclusivity. -/
theorem sameWitnessOverlap :
    ∃ x r, (model.InPotency x r ∧ ∀ y, model.InAct y r → ¬ model.PriorSimply y x) ∧
      model.MovedIn x r ∧ ActualSelfMoverAt model.InAct model.MovesIn x r ∧
      NonpriorOtherActualMoverAt model.InAct model.MovesIn model.PriorSimply x r := by decide

theorem reducedActual : ReducedOnlyByABeingInActReading model.MovedIn model.MovesIn
    model.InAct := by decide

theorem mover : ReducedOnlyByAMoverReading model.MovedIn model.MovesIn := by decide

theorem actual : MovesOnlyAsInActReading model.MovesIn model.InAct := by decide

theorem violatesNotBoth :
    ¬ NotActAndPotencyInSameRespectReading model.InAct model.InPotency := by decide

theorem violatesNoSelf :
    ¬ NothingMovesItselfInSameRespectReading model.MovedIn model.MovesIn := by decide

theorem violatesPrior :
    ¬ ActualMoverIsSimplyPriorReading model.InAct model.InPotency model.MovesIn
      model.PriorSimply := by decide
end Overlap

namespace NonactualMover
def model : TruthCore.Models.NightCosmogony.Model where
  InAct := fun _ _ => False
  InPotency := fun _ _ => True
  MovedIn := fun _ _ => True
  MovesIn := fun _ _ _ => True
  PriorSimply := fun _ _ => False

theorem background : UnprecededPotencyActualizedReading model.InAct model.InPotency
    model.MovedIn model.PriorSimply := by decide

theorem fork : NightActualizationFork model.InAct model.InPotency model.MovedIn
    model.MovesIn model.PriorSimply := by decide

/-- Lacking an actual mover does not mean lacking a mover: both conjuncts
hold for the same moved potency in this interpretation. -/
theorem nonactualMover :
    NoActualMoverAt model.InAct model.MovesIn false () ∧
      ∃ y, model.MovesIn y false () := by decide

theorem mover : ReducedOnlyByAMoverReading model.MovedIn model.MovesIn := by decide

theorem violatesActual : ¬ MovesOnlyAsInActReading model.MovesIn model.InAct := by decide

theorem violatesReducedActual :
    ¬ ReducedOnlyByABeingInActReading model.MovedIn model.MovesIn model.InAct := by decide

theorem notBoth : NotActAndPotencyInSameRespectReading model.InAct model.InPotency := by decide

theorem noForcedBranch : ¬ NightNonpriorOtherActualMover model.InAct model.InPotency
    model.MovedIn model.MovesIn model.PriorSimply := by decide

theorem priority : ActualMoverIsSimplyPriorReading model.InAct model.InPotency
    model.MovesIn model.PriorSimply := by decide
end NonactualMover

end TruthCore.Models.NightActualizationFork
