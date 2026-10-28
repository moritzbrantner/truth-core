import TruthCore.Modal.Convergence

/-! Transparent delivery bundle of the existing exact-length modal
correspondence helpers; this adds no new mathematical or philosophical claim
beyond their conjunction. -/
namespace TruthCore.Modal
universe u v

/-- Exact path semantics, arbitrary-formula soundness, one-atom all-valuation
correspondence and the 4/B/5 instances. No global frame assumptions or world
population are imposed, and no Hilbert completeness claim is included. -/
def ConvergenceCertificate : Prop :=
  (∀ (World : Type u) (F : Frame World) a b, ExactPath F 0 a b ↔ a = b) ∧
  (∀ (World : Type u) (F : Frame World) n a b,
    ExactPath F (n + 1) a b ↔ ∃ c, F.access a c ∧ ExactPath F n c b) ∧
  (∀ (World : Type u) (Atom : Type v) (F : Frame World)
    (V : Valuation World Atom) (φ : Formula Atom) n a,
    Holds F V a (.iterBox n φ) ↔ ∀ b, ExactPath F n a b → Holds F V b φ) ∧
  (∀ (World : Type u) (Atom : Type v) (F : Frame World)
    (V : Valuation World Atom) (φ : Formula Atom) n a,
    Holds F V a (.iterDiamond n φ) ↔ ∃ b, ExactPath F n a b ∧ Holds F V b φ) ∧
  (∀ (World : Type u) (Atom : Type v) (F : Frame World) h i j k,
    Convergent F h i j k → ∀ (φ : Formula Atom),
    Valid F (.imp (.iterDiamond h (.iterBox i φ)) (.iterBox j (.iterDiamond k φ)))) ∧
  (∀ (World : Type u) (F : Frame World) h i j k,
    Convergent F h i j k ↔ Valid F (convergenceFormula h i j k)) ∧
  (∀ (World : Type u) (F : Frame World),
    Transitive F ↔ Valid F (convergenceFormula 0 1 2 0)) ∧
  (∀ (World : Type u) (F : Frame World),
    Symmetric F ↔ Valid F (convergenceFormula 0 0 1 1)) ∧
  (∀ (World : Type u) (F : Frame World),
    Euclidean F ↔ Valid F (convergenceFormula 1 0 1 1))

end TruthCore.Modal
