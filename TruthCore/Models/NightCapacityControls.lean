import TruthCore.Models.NightActualizationFork
import TruthCore.Models.NightMovingResidual
import TruthCore.Results.Bridges.AristPotencyAnalysisNonSimultaneity.Solution

/-! Capacity extensions of the seven existing Night interpretations. Their
beings, respects, act, potency, motion, moving and simple-priority assignments
are unchanged. In every extension `CanBe x r := InPotency x r ∨ InAct x r`;
thus actuality implies ability in these chosen interpretations too.

The analysis of potency holds in the five interpretations that satisfy
same-respect act/potency exclusion. It fails in SelfMover and Overlap by the
existing analysis-to-exclusion bridge. These are joint finite controls of the
six-atom territory projection, not complete accounts of Aristotelian capacity,
metaphysical possibilities, or defenses of any root premise. -/
namespace TruthCore.Models.NightCapacityControls

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Results.Bridges.AristPotencyAnalysisNonSimultaneity

private theorem capacityAnalysis {Being Respect : Type}
    (InAct InPotency : Being → Respect → Prop)
    (h : NotActAndPotencyInSameRespectReading InAct InPotency) :
    PotencyIsUnactualizedCapacityReading InAct InPotency
      (fun x r => InPotency x r ∨ InAct x r) := by
  intro x r
  constructor
  · intro hPotency
    exact ⟨Or.inl hPotency, fun hAct => h x r ⟨hAct, hPotency⟩⟩
  · intro hCapacity
    exact hCapacity.1.elim id (fun hAct => (hCapacity.2 hAct).elim)

namespace NoReduction
abbrev model := TruthCore.Models.NightCosmogony.NoReduction.model
def canBe (x : Bool) (r : Unit) : Prop := model.InPotency x r ∨ model.InAct x r

theorem analysis : PotencyIsUnactualizedCapacityReading model.InAct model.InPotency canBe :=
  capacityAnalysis model.InAct model.InPotency
    TruthCore.Models.NightActualizationFork.NoReduction.notBoth
end NoReduction

namespace SelfMover
abbrev model := TruthCore.Models.NightCosmogony.SelfMover.model
def canBe (x : Bool) (r : Unit) : Prop := model.InPotency x r ∨ model.InAct x r

theorem violatesAnalysis :
    ¬ PotencyIsUnactualizedCapacityReading model.InAct model.InPotency canBe :=
  fun h => TruthCore.Models.NightActualizationFork.SelfMover.violatesNotBoth
    (notActAndPotencyOfPotencyAnalysis model.InAct model.InPotency canBe h)
end SelfMover

namespace Residual
abbrev model := TruthCore.Models.NightCosmogony.Residual.model
def canBe (x : Bool) (r : Unit) : Prop := model.InPotency x r ∨ model.InAct x r

theorem analysis : PotencyIsUnactualizedCapacityReading model.InAct model.InPotency canBe :=
  capacityAnalysis model.InAct model.InPotency
    TruthCore.Models.NightActualizationFork.Residual.notBoth
end Residual

namespace OtherMover
abbrev model := TruthCore.Models.NightCosmogony.OtherMover.model
def canBe (x : Bool) (r : Unit) : Prop := model.InPotency x r ∨ model.InAct x r

theorem analysis : PotencyIsUnactualizedCapacityReading model.InAct model.InPotency canBe :=
  capacityAnalysis model.InAct model.InPotency
    TruthCore.Models.NightActualizationFork.OtherMover.notBoth
end OtherMover

namespace NonactualMover
abbrev model := TruthCore.Models.NightActualizationFork.NonactualMover.model
def canBe (x : Bool) (r : Unit) : Prop := model.InPotency x r ∨ model.InAct x r

theorem analysis : PotencyIsUnactualizedCapacityReading model.InAct model.InPotency canBe :=
  capacityAnalysis model.InAct model.InPotency
    TruthCore.Models.NightActualizationFork.NonactualMover.notBoth
end NonactualMover

namespace Overlap
abbrev model := TruthCore.Models.NightActualizationFork.Overlap.model
def canBe (x : Bool) (r : Unit) : Prop := model.InPotency x r ∨ model.InAct x r

theorem violatesAnalysis :
    ¬ PotencyIsUnactualizedCapacityReading model.InAct model.InPotency canBe :=
  fun h => TruthCore.Models.NightActualizationFork.Overlap.violatesNotBoth
    (notActAndPotencyOfPotencyAnalysis model.InAct model.InPotency canBe h)
end Overlap

namespace MovingResidual
abbrev model := TruthCore.Models.NightMovingResidual.model
def canBe (x : TruthCore.Models.NightMovingResidual.Being) (r : Unit) : Prop :=
  model.InPotency x r ∨ model.InAct x r

theorem analysis : PotencyIsUnactualizedCapacityReading model.InAct model.InPotency canBe :=
  capacityAnalysis model.InAct model.InPotency TruthCore.Models.NightMovingResidual.evaluation3
end MovingResidual

end TruthCore.Models.NightCapacityControls
