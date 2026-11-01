import TruthCore.Mereology.FusionNoNecessaryParts

/-!
Analyst selected-fusion reconstruction of the displayed L2 part-extraction step.
Source A1/A2/L2 are not bound to these heads. The necessity of the selected
fusion is a separate OPEN premise, not inferred from local parts-to-whole
existence or from necessity of its members. All orders and modal domains remain
fixed; no actual existence, cause, root, or ordinary contingency is asserted.
-/
namespace TruthCore.Mereology.NecessaryPartFusionDecomposition
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.FusionNoNecessaryParts

/-- Nonnecessity alone, with no actual-presence or concrete-domain guard. -/
def NotNecessaryAt {W B : Type} (m : Ontic W B) (w : W) (x : B) : Prop :=
  ¬ NecessaryAt m w x

/-- Explicit overlap-extensional parthood over the supplied Mathlib order.
The implication from overlap inclusion to parthood is not a partial-order law. -/
def OverlapExtensionalParthood (B : Type) [PartialOrder B] : Prop :=
  ∀ x y : B, x ≤ y ↔ ∀ z, Overlap z x → Overlap z y

/-- Exactly the necessary parts of THIS selected x at THIS modal standpoint. -/
def necessaryParts {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (x : B) : Set B :=
  {p | p ≤ x ∧ NecessaryAt m w p}

/-- Only when this selected necessary-parts family is nonempty, an existing
Sum2 fusion can be chosen which itself satisfies NecessaryAt. This is not
unrestricted fusion, actual existence, or a theorem from local A5. -/
def SelectedNecessaryPartsFusionAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (x : B) : Prop :=
  (necessaryParts m w x).Nonempty →
    ∃ n, Fusion (necessaryParts m w x) n ∧ NecessaryAt m w n

/-- A part without necessary parts; no actual presence or properness asserted. -/
def HasNoNecessaryPartsPartAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (x : B) : Prop :=
  ∃ q, q ≤ x ∧ NoNecessaryPartsAt m w q

end TruthCore.Mereology.NecessaryPartFusionDecomposition
