import TruthCore.Models.FiniteSupport
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.Order
open TruthCore.Models.FiniteSupport
/-- Constructive instances of Mathlib's Preorder. The larger global Boolean
order instance carries axioms in unused proof fields, so these finite certificates
supply exactly the order structure they use. -/
abbrev boolOrder : Preorder Bool where
  le a b := a = false ∨ b = true
  lt a b := a = false ∧ b = true
  le_refl := by intro a; cases a; exact Or.inl rfl; exact Or.inr rfl
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  lt_iff_le_not_ge := by intro a b; cases a <;> cases b <;> decide

abbrev unitOrder : Preorder Unit where
  le _ _ := True
  lt _ _ := False
  le_refl := fun _ => trivial
  le_trans := fun _ _ _ _ _ => trivial
  lt_iff_le_not_ge := fun _ _ => ⟨False.elim, fun h => h.2 trivial⟩

structure Model (Degree : Type) where
  InAct : Bool → Unit → Prop
  MoreIn : Unit → Bool → Bool → Prop
  CausesIn : Bool → Bool → Unit → Prop
  Creature : Bool → Prop
  PriorSimply : Bool → Bool → Prop
  near : Bool → Degree
  primary : Bool
  esse : Unit
namespace NoCausalOrder
abbrev order : Preorder Bool := boolOrder
abbrev beingOrder : Preorder Bool := boolOrder
def model : Model Bool where
  InAct := fun _ _ => True
  MoreIn := fun _ x y => y = false ∧ x = true
  CausesIn := fun _ _ _ => False
  Creature := fun _ => True
  PriorSimply := fun _ _ => False
  near := id
  primary := true
  esse := ()
theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.ApproachToPrimaryReading (Bool) (Unit) (Bool) (TruthCore.Models.Order.NoCausalOrder.order) (TruthCore.Models.Order.NoCausalOrder.model.InAct) (TruthCore.Models.Order.NoCausalOrder.model.MoreIn) (TruthCore.Models.Order.NoCausalOrder.model.esse) (TruthCore.Models.Order.NoCausalOrder.model.near) (TruthCore.Models.Order.NoCausalOrder.model.primary) := by exact ⟨trivial, fun _ _ => Iff.rfl⟩

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading (Bool) (Bool) (TruthCore.Models.Order.NoCausalOrder.order) (TruthCore.Models.Order.NoCausalOrder.model.near) (TruthCore.Models.Order.NoCausalOrder.model.primary) := by
  intro x hx
  cases x
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl hx

theorem evaluation2 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading (Bool) (Unit) (TruthCore.Models.Order.NoCausalOrder.model.InAct) (TruthCore.Models.Order.NoCausalOrder.model.CausesIn) (TruthCore.Models.Order.NoCausalOrder.model.Creature) (TruthCore.Models.Order.NoCausalOrder.model.esse) (TruthCore.Models.Order.NoCausalOrder.model.primary)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading
  decide

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading (Bool) (TruthCore.Models.Order.NoCausalOrder.model.Creature) (TruthCore.Models.Order.NoCausalOrder.model.primary) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
  decide

theorem evaluation4 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading (Bool) (Unit) (TruthCore.Models.Order.NoCausalOrder.model.InAct) (TruthCore.Models.Order.NoCausalOrder.model.MoreIn) (TruthCore.Models.Order.NoCausalOrder.model.CausesIn) (TruthCore.Models.Order.NoCausalOrder.model.esse)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation5 : @TruthCore.Case.Catholicism.AtMostOneMaximeEns (Bool) (Unit) (TruthCore.Models.Order.NoCausalOrder.model.InAct) (TruthCore.Models.Order.NoCausalOrder.model.MoreIn) (TruthCore.Models.Order.NoCausalOrder.model.esse) := by
  unfold model TruthCore.Case.Catholicism.AtMostOneMaximeEns TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  decide

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading (Bool) (Unit) (TruthCore.Models.Order.NoCausalOrder.model.InAct) (TruthCore.Models.Order.NoCausalOrder.model.MoreIn) (TruthCore.Models.Order.NoCausalOrder.model.CausesIn)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation7 : @TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading (Bool) (Unit) (TruthCore.Models.Order.NoCausalOrder.model.CausesIn) (TruthCore.Models.Order.NoCausalOrder.model.MoreIn) := by
  unfold model TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  decide

theorem evaluation8 : @TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing (Bool) (Unit) (TruthCore.Models.Order.NoCausalOrder.model.PriorSimply) (TruthCore.Models.Order.NoCausalOrder.model.CausesIn) (TruthCore.Models.Order.NoCausalOrder.model.esse) := by
  unfold model TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing
  decide

theorem evaluation9 : @TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing (Bool) (Unit) (TruthCore.Models.Order.NoCausalOrder.model.InAct) (TruthCore.Models.Order.NoCausalOrder.model.MoreIn) (TruthCore.Models.Order.NoCausalOrder.model.esse) (TruthCore.Models.Order.NoCausalOrder.model.PriorSimply) := by
  unfold model TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing
  decide

theorem evaluation10 : @TruthCore.Latin.Aquinas.SummaTheologiae.HomogeneousScaleReading (Bool) (Unit) (TruthCore.Models.Order.NoCausalOrder.beingOrder) (TruthCore.Models.Order.NoCausalOrder.model.InAct) (TruthCore.Models.Order.NoCausalOrder.model.MoreIn) (TruthCore.Models.Order.NoCausalOrder.model.esse) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.HomogeneousScaleReading beingOrder boolOrder
  exact ⟨fun _ => trivial, fun _ _ => Iff.rfl⟩

end NoCausalOrder
namespace NoCreatures
abbrev order : Preorder Bool := boolOrder
abbrev beingOrder : Preorder Bool := boolOrder
def model : Model Bool where
  InAct := fun _ _ => True
  MoreIn := fun _ x y => y = false ∧ x = true
  CausesIn := fun _ _ _ => False
  Creature := fun _ => False
  PriorSimply := fun _ _ => False
  near := id
  primary := true
  esse := ()
theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.ApproachToPrimaryReading (Bool) (Unit) (Bool) (TruthCore.Models.Order.NoCreatures.order) (TruthCore.Models.Order.NoCreatures.model.InAct) (TruthCore.Models.Order.NoCreatures.model.MoreIn) (TruthCore.Models.Order.NoCreatures.model.esse) (TruthCore.Models.Order.NoCreatures.model.near) (TruthCore.Models.Order.NoCreatures.model.primary) := by exact ⟨trivial, fun _ _ => Iff.rfl⟩

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading (Bool) (Bool) (TruthCore.Models.Order.NoCreatures.order) (TruthCore.Models.Order.NoCreatures.model.near) (TruthCore.Models.Order.NoCreatures.model.primary) := by
  intro x hx
  cases x
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl hx

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading (Bool) (Unit) (TruthCore.Models.Order.NoCreatures.model.InAct) (TruthCore.Models.Order.NoCreatures.model.CausesIn) (TruthCore.Models.Order.NoCreatures.model.Creature) (TruthCore.Models.Order.NoCreatures.model.esse) (TruthCore.Models.Order.NoCreatures.model.primary) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading
  decide

theorem evaluation3 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading (Bool) (TruthCore.Models.Order.NoCreatures.model.Creature) (TruthCore.Models.Order.NoCreatures.model.primary)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
  decide

theorem evaluation4 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading (Bool) (Unit) (TruthCore.Models.Order.NoCreatures.model.InAct) (TruthCore.Models.Order.NoCreatures.model.MoreIn) (TruthCore.Models.Order.NoCreatures.model.CausesIn) (TruthCore.Models.Order.NoCreatures.model.esse)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation5 : @TruthCore.Case.Catholicism.AtMostOneMaximeEns (Bool) (Unit) (TruthCore.Models.Order.NoCreatures.model.InAct) (TruthCore.Models.Order.NoCreatures.model.MoreIn) (TruthCore.Models.Order.NoCreatures.model.esse) := by
  unfold model TruthCore.Case.Catholicism.AtMostOneMaximeEns TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  decide

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading (Bool) (Unit) (TruthCore.Models.Order.NoCreatures.model.InAct) (TruthCore.Models.Order.NoCreatures.model.MoreIn) (TruthCore.Models.Order.NoCreatures.model.CausesIn)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation7 : @TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading (Bool) (Unit) (TruthCore.Models.Order.NoCreatures.model.CausesIn) (TruthCore.Models.Order.NoCreatures.model.MoreIn) := by
  unfold model TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  decide

theorem evaluation8 : @TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing (Bool) (Unit) (TruthCore.Models.Order.NoCreatures.model.PriorSimply) (TruthCore.Models.Order.NoCreatures.model.CausesIn) (TruthCore.Models.Order.NoCreatures.model.esse) := by
  unfold model TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing
  decide

theorem evaluation9 : @TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing (Bool) (Unit) (TruthCore.Models.Order.NoCreatures.model.InAct) (TruthCore.Models.Order.NoCreatures.model.MoreIn) (TruthCore.Models.Order.NoCreatures.model.esse) (TruthCore.Models.Order.NoCreatures.model.PriorSimply) := by
  unfold model TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing
  decide

theorem evaluation10 : @TruthCore.Latin.Aquinas.SummaTheologiae.HomogeneousScaleReading (Bool) (Unit) (TruthCore.Models.Order.NoCreatures.beingOrder) (TruthCore.Models.Order.NoCreatures.model.InAct) (TruthCore.Models.Order.NoCreatures.model.MoreIn) (TruthCore.Models.Order.NoCreatures.model.esse) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.HomogeneousScaleReading beingOrder boolOrder
  exact ⟨fun _ => trivial, fun _ _ => Iff.rfl⟩

end NoCreatures
namespace TiedPrimary
abbrev order : Preorder Unit := unitOrder
abbrev beingOrder : Preorder Bool := boolOrder
def model : Model Unit where
  InAct := fun _ _ => True
  MoreIn := fun _ _ _ => False
  CausesIn := fun c x _ => c = true ∧ x ≠ true
  Creature := fun x => x ≠ true
  PriorSimply := fun _ _ => False
  near := fun _ => ()
  primary := true
  esse := ()
theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.ApproachToPrimaryReading (Bool) (Unit) (Unit) (TruthCore.Models.Order.TiedPrimary.order) (TruthCore.Models.Order.TiedPrimary.model.InAct) (TruthCore.Models.Order.TiedPrimary.model.MoreIn) (TruthCore.Models.Order.TiedPrimary.model.esse) (TruthCore.Models.Order.TiedPrimary.model.near) (TruthCore.Models.Order.TiedPrimary.model.primary) := by exact ⟨trivial, fun _ _ => Iff.rfl⟩

theorem evaluation1 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading (Bool) (Unit) (TruthCore.Models.Order.TiedPrimary.order) (TruthCore.Models.Order.TiedPrimary.model.near) (TruthCore.Models.Order.TiedPrimary.model.primary)) := by
  intro h
  exact h false (by decide)

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading (Bool) (Unit) (TruthCore.Models.Order.TiedPrimary.model.InAct) (TruthCore.Models.Order.TiedPrimary.model.CausesIn) (TruthCore.Models.Order.TiedPrimary.model.Creature) (TruthCore.Models.Order.TiedPrimary.model.esse) (TruthCore.Models.Order.TiedPrimary.model.primary) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading
  decide

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading (Bool) (TruthCore.Models.Order.TiedPrimary.model.Creature) (TruthCore.Models.Order.TiedPrimary.model.primary) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
  decide

theorem evaluation4 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading (Bool) (Unit) (TruthCore.Models.Order.TiedPrimary.model.InAct) (TruthCore.Models.Order.TiedPrimary.model.MoreIn) (TruthCore.Models.Order.TiedPrimary.model.CausesIn) (TruthCore.Models.Order.TiedPrimary.model.esse)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation5 : ¬ (@TruthCore.Case.Catholicism.AtMostOneMaximeEns (Bool) (Unit) (TruthCore.Models.Order.TiedPrimary.model.InAct) (TruthCore.Models.Order.TiedPrimary.model.MoreIn) (TruthCore.Models.Order.TiedPrimary.model.esse)) := by
  unfold model TruthCore.Case.Catholicism.AtMostOneMaximeEns TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  decide

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading (Bool) (Unit) (TruthCore.Models.Order.TiedPrimary.model.InAct) (TruthCore.Models.Order.TiedPrimary.model.MoreIn) (TruthCore.Models.Order.TiedPrimary.model.CausesIn)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation7 : ¬ (@TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading (Bool) (Unit) (TruthCore.Models.Order.TiedPrimary.model.CausesIn) (TruthCore.Models.Order.TiedPrimary.model.MoreIn)) := by
  unfold model TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  decide

theorem evaluation8 : @TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing (Bool) (Unit) (TruthCore.Models.Order.TiedPrimary.model.PriorSimply) (TruthCore.Models.Order.TiedPrimary.model.CausesIn) (TruthCore.Models.Order.TiedPrimary.model.esse) := by
  unfold model TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing
  decide

theorem evaluation9 : @TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing (Bool) (Unit) (TruthCore.Models.Order.TiedPrimary.model.InAct) (TruthCore.Models.Order.TiedPrimary.model.MoreIn) (TruthCore.Models.Order.TiedPrimary.model.esse) (TruthCore.Models.Order.TiedPrimary.model.PriorSimply) := by
  unfold model TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing
  decide

end TiedPrimary
namespace MutualCauseAndPriority
abbrev order : Preorder Bool := boolOrder
abbrev beingOrder : Preorder Bool := boolOrder
def model : Model Bool where
  InAct := fun _ _ => True
  MoreIn := fun _ x y => y = false ∧ x = true
  CausesIn := fun c x _ => c ≠ x
  Creature := fun x => x ≠ true
  PriorSimply := fun c x => c ≠ x
  near := id
  primary := true
  esse := ()
theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.ApproachToPrimaryReading (Bool) (Unit) (Bool) (TruthCore.Models.Order.MutualCauseAndPriority.order) (TruthCore.Models.Order.MutualCauseAndPriority.model.InAct) (TruthCore.Models.Order.MutualCauseAndPriority.model.MoreIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.esse) (TruthCore.Models.Order.MutualCauseAndPriority.model.near) (TruthCore.Models.Order.MutualCauseAndPriority.model.primary) := by exact ⟨trivial, fun _ _ => Iff.rfl⟩

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading (Bool) (Bool) (TruthCore.Models.Order.MutualCauseAndPriority.order) (TruthCore.Models.Order.MutualCauseAndPriority.model.near) (TruthCore.Models.Order.MutualCauseAndPriority.model.primary) := by
  intro x hx
  cases x
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl hx

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading (Bool) (Unit) (TruthCore.Models.Order.MutualCauseAndPriority.model.InAct) (TruthCore.Models.Order.MutualCauseAndPriority.model.CausesIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.Creature) (TruthCore.Models.Order.MutualCauseAndPriority.model.esse) (TruthCore.Models.Order.MutualCauseAndPriority.model.primary) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading
  decide

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading (Bool) (TruthCore.Models.Order.MutualCauseAndPriority.model.Creature) (TruthCore.Models.Order.MutualCauseAndPriority.model.primary) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
  decide

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading (Bool) (Unit) (TruthCore.Models.Order.MutualCauseAndPriority.model.InAct) (TruthCore.Models.Order.MutualCauseAndPriority.model.MoreIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.CausesIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.esse) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation5 : @TruthCore.Case.Catholicism.AtMostOneMaximeEns (Bool) (Unit) (TruthCore.Models.Order.MutualCauseAndPriority.model.InAct) (TruthCore.Models.Order.MutualCauseAndPriority.model.MoreIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.esse) := by
  unfold model TruthCore.Case.Catholicism.AtMostOneMaximeEns TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  decide

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading (Bool) (Unit) (TruthCore.Models.Order.MutualCauseAndPriority.model.InAct) (TruthCore.Models.Order.MutualCauseAndPriority.model.MoreIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.CausesIn) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation7 : ¬ (@TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading (Bool) (Unit) (TruthCore.Models.Order.MutualCauseAndPriority.model.CausesIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.MoreIn)) := by
  unfold model TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  decide

theorem evaluation8 : @TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing (Bool) (Unit) (TruthCore.Models.Order.MutualCauseAndPriority.model.PriorSimply) (TruthCore.Models.Order.MutualCauseAndPriority.model.CausesIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.esse) := by
  unfold model TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing
  decide

theorem evaluation9 : ¬ (@TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing (Bool) (Unit) (TruthCore.Models.Order.MutualCauseAndPriority.model.InAct) (TruthCore.Models.Order.MutualCauseAndPriority.model.MoreIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.esse) (TruthCore.Models.Order.MutualCauseAndPriority.model.PriorSimply)) := by
  unfold model TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing
  decide

theorem evaluation10 : @TruthCore.Latin.Aquinas.SummaTheologiae.HomogeneousScaleReading (Bool) (Unit) (TruthCore.Models.Order.MutualCauseAndPriority.beingOrder) (TruthCore.Models.Order.MutualCauseAndPriority.model.InAct) (TruthCore.Models.Order.MutualCauseAndPriority.model.MoreIn) (TruthCore.Models.Order.MutualCauseAndPriority.model.esse) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.HomogeneousScaleReading beingOrder boolOrder
  exact ⟨fun _ => trivial, fun _ _ => Iff.rfl⟩

end MutualCauseAndPriority
namespace HomogeneousCausalControl
abbrev order : Preorder Bool := boolOrder
abbrev beingOrder : Preorder Bool := boolOrder
def model : Model Bool where
  InAct := fun _ _ => True
  MoreIn := fun _ x y => y = false ∧ x = true
  CausesIn := fun c x _ => c = true ∧ x = false
  Creature := fun x => x ≠ true
  PriorSimply := fun _ _ => False
  near := id
  primary := true
  esse := ()
theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.ApproachToPrimaryReading (Bool) (Unit) (Bool) (TruthCore.Models.Order.HomogeneousCausalControl.order) (TruthCore.Models.Order.HomogeneousCausalControl.model.InAct) (TruthCore.Models.Order.HomogeneousCausalControl.model.MoreIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.esse) (TruthCore.Models.Order.HomogeneousCausalControl.model.near) (TruthCore.Models.Order.HomogeneousCausalControl.model.primary) := by exact ⟨trivial, fun _ _ => Iff.rfl⟩

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading (Bool) (Bool) (TruthCore.Models.Order.HomogeneousCausalControl.order) (TruthCore.Models.Order.HomogeneousCausalControl.model.near) (TruthCore.Models.Order.HomogeneousCausalControl.model.primary) := by
  intro x hx
  cases x
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl hx

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading (Bool) (Unit) (TruthCore.Models.Order.HomogeneousCausalControl.model.InAct) (TruthCore.Models.Order.HomogeneousCausalControl.model.CausesIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.Creature) (TruthCore.Models.Order.HomogeneousCausalControl.model.esse) (TruthCore.Models.Order.HomogeneousCausalControl.model.primary) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading
  decide

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading (Bool) (TruthCore.Models.Order.HomogeneousCausalControl.model.Creature) (TruthCore.Models.Order.HomogeneousCausalControl.model.primary) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
  decide

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading (Bool) (Unit) (TruthCore.Models.Order.HomogeneousCausalControl.model.InAct) (TruthCore.Models.Order.HomogeneousCausalControl.model.MoreIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.CausesIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.esse) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInBeingCausesAllBeingsReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation5 : @TruthCore.Case.Catholicism.AtMostOneMaximeEns (Bool) (Unit) (TruthCore.Models.Order.HomogeneousCausalControl.model.InAct) (TruthCore.Models.Order.HomogeneousCausalControl.model.MoreIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.esse) := by
  unfold model TruthCore.Case.Catholicism.AtMostOneMaximeEns TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  decide

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading (Bool) (Unit) (TruthCore.Models.Order.HomogeneousCausalControl.model.InAct) (TruthCore.Models.Order.HomogeneousCausalControl.model.MoreIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.CausesIn) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

theorem evaluation7 : @TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading (Bool) (Unit) (TruthCore.Models.Order.HomogeneousCausalControl.model.CausesIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.MoreIn) := by
  unfold model TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  decide

theorem evaluation8 : @TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing (Bool) (Unit) (TruthCore.Models.Order.HomogeneousCausalControl.model.PriorSimply) (TruthCore.Models.Order.HomogeneousCausalControl.model.CausesIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.esse) := by
  unfold model TruthCore.Case.Catholicism.SimplyPriorIsCauseOfBeing
  decide

theorem evaluation9 : @TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing (Bool) (Unit) (TruthCore.Models.Order.HomogeneousCausalControl.model.InAct) (TruthCore.Models.Order.HomogeneousCausalControl.model.MoreIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.esse) (TruthCore.Models.Order.HomogeneousCausalControl.model.PriorSimply) := by
  unfold model TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing
  decide

theorem evaluation10 : @TruthCore.Latin.Aquinas.SummaTheologiae.HomogeneousScaleReading (Bool) (Unit) (TruthCore.Models.Order.HomogeneousCausalControl.beingOrder) (TruthCore.Models.Order.HomogeneousCausalControl.model.InAct) (TruthCore.Models.Order.HomogeneousCausalControl.model.MoreIn) (TruthCore.Models.Order.HomogeneousCausalControl.model.esse) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.HomogeneousScaleReading beingOrder boolOrder
  exact ⟨fun _ => trivial, fun _ _ => Iff.rfl⟩

end HomogeneousCausalControl
end TruthCore.Models.Order
