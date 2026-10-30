import TruthCore.Modal.GraphBridge

/-! Exact finite path correspondence for modal convergence schemas. Path length
is Mathlib's Quiver.Path.length, not reflexive-transitive reachability. These
are frame correspondences, not Hilbert completeness or canonical-model claims. -/
namespace TruthCore.Modal
universe u v
namespace Formula
variable {Atom : Type v}
def iterBox : Nat → Formula Atom → Formula Atom
  | 0, φ => φ
  | n + 1, φ => .box (iterBox n φ)
def iterDiamond : Nat → Formula Atom → Formula Atom
  | 0, φ => φ
  | n + 1, φ => .diamond (iterDiamond n φ)
end Formula

/-- Witness-oriented use of Mathlib's exact-length path notion. -/
def ExactPath {World : Type u} (F : Frame World) (n : Nat) (a b : World) : Prop :=
  ∃ p : @Quiver.Path World F.toQuiver a b, @Quiver.Path.length World F.toQuiver a b p = n

/-- Every h/j fork has an i/k join, with lengths in the displayed direction. -/
def Convergent {World : Type u} (F : Frame World) (h i j k : Nat) : Prop :=
  ∀ w a b, ExactPath F h w a → ExactPath F j w b →
    ∃ c, ExactPath F i a c ∧ ExactPath F k b c

/-- The one-atom instance suffices for full valuation correspondence. -/
def convergenceFormula (h i j k : Nat) : Formula Unit :=
  .imp (.iterDiamond h (.iterBox i (.atom ())))
    (.iterBox j (.iterDiamond k (.atom ())))
end TruthCore.Modal
