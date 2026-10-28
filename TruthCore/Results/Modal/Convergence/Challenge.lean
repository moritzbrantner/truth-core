import TruthCore.Modal.Convergence

namespace TruthCore.Results.Modal.Convergence
open TruthCore.Modal
universe u v

theorem exactPath_zero {World : Type u} (F : Frame World) (a b : World) :
    ExactPath F 0 a b ↔ a = b := by
  sorry

theorem exactPath_succ {World : Type u} (F : Frame World) (n : Nat) (a b : World) :
    ExactPath F (n + 1) a b ↔ ∃ c, F.access a c ∧ ExactPath F n c b := by
  sorry

theorem iterBox_semantics {World : Type u} {Atom : Type v} (F : Frame World)
    (V : Valuation World Atom) (φ : Formula Atom) (n : Nat) (a : World) :
    Holds F V a (.iterBox n φ) ↔ ∀ b, ExactPath F n a b → Holds F V b φ := by
  sorry

theorem iterDiamond_semantics {World : Type u} {Atom : Type v} (F : Frame World)
    (V : Valuation World Atom) (φ : Formula Atom) (n : Nat) (a : World) :
    Holds F V a (.iterDiamond n φ) ↔ ∃ b, ExactPath F n a b ∧ Holds F V b φ := by
  sorry

/-- Soundness covers arbitrary formulas, not only the one-atom test. -/
theorem convergence_sound {World : Type u} {Atom : Type v} (F : Frame World)
    (h i j k : Nat) (hc : Convergent F h i j k) (φ : Formula Atom) :
    Valid F (.imp (.iterDiamond h (.iterBox i φ)) (.iterBox j (.iterDiamond k φ))) := by
  sorry

/-- Characteristic valuations give correspondence, without a completeness claim. -/
theorem convergence_iff_valid {World : Type u} (F : Frame World) (h i j k : Nat) :
    Convergent F h i j k ↔ Valid F (convergenceFormula h i j k) := by
  sorry

theorem axiom4_correspondence {World : Type u} (F : Frame World) :
    Transitive F ↔ Valid F (convergenceFormula 0 1 2 0) := by
  sorry

theorem axiomB_correspondence {World : Type u} (F : Frame World) :
    Symmetric F ↔ Valid F (convergenceFormula 0 0 1 1) := by
  sorry

theorem axiom5_correspondence {World : Type u} (F : Frame World) :
    Euclidean F ↔ Valid F (convergenceFormula 1 0 1 1) := by
  sorry
end TruthCore.Results.Modal.Convergence
