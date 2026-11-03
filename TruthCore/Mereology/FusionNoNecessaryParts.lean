import TruthCore.Mereology.UniversalFusionBoundary
import TruthCore.German.Kant.CosmologicalInference

/-!
Analyst reconstruction of a structural L3 step, not a binding of the source's
wholly-contingent or modal-parthood assertions. Reuses fixed Mathlib parthood,
existing Sum2 Fusion/Overlap and Ontic NecessaryAt. Existence of a value in the
carrier or of its fusion does not assert Ontic existence at any world.
-/
namespace TruthCore.Mereology.FusionNoNecessaryParts
open TruthCore.German.Kant.CosmologicalInference

/-- No part, including the object itself under reflexive parthood, satisfies
the existing NecessaryAt. This asserts no actual existence or ContingentAt. -/
def NoNecessaryPartsAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (x : B) : Prop :=
  ∀ p, p ≤ x → ¬ NecessaryAt m w p

/-- Every selected family member has no necessary parts, at THIS standpoint
and in the SAME fixed parthood/ontology. No actual population is asserted. -/
def FamilyNoNecessaryPartsAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (family : Set B) : Prop :=
  ∀ x ∈ family, NoNecessaryPartsAt m w x

/-- OPEN modal-parthood premise, not a consequence of order alone or merely
actual-world part existence. Relating this to source A4 requires a defended
cross-world scope and persistence/rigidity of the relevant parthood. -/
def NecessityDownwardAlongParthoodAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) : Prop :=
  ∀ x p, p ≤ x → NecessaryAt m w x → NecessaryAt m w p

end TruthCore.Mereology.FusionNoNecessaryParts
