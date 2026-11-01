import TruthCore.Mereology.FusionNoNecessaryParts

/-!
Analyst whole-route consumer, not a source binding of A2/A4/C1–3. The actual
selected fusion and all causal/part-existence policies are explicit. No profile,
concreteness dictionary, L1/L2 warrant, modal frame law or model is introduced.
The conclusion is SOME actual necessary individual, not a necessary cause.
-/
namespace TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.FusionNoNecessaryParts

/-- Actual candidates without necessary parts at this SAME standpoint. -/
def ActualNoNecessaryPartsFamily {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) : Set B :=
  {x | m.ExistsAt w x ∧ NoNecessaryPartsAt m w x}

/-- Explicit actual sum AND existing Sum2 fusion of the selected actual family.
A carrier value or abstract fusion alone does not supply this actuality. -/
def ActualFusionAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (sum : B) : Prop :=
  m.ExistsAt w sum ∧ Fusion (ActualNoNecessaryPartsFamily m w) sum

/-- Actual-whole/actual-parts policy only at the selected world. No modal
necessity-downward or cross-world part-persistence law is included. -/
def ActualPartsExistAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) : Prop :=
  ∀ x p, m.ExistsAt w x → p ≤ x → m.ExistsAt w p

/-- OPEN causal input for actual no-necessary-parts candidates, not ordinary
PSR, explanations, all modal contingents or causation inferred by definition. -/
def ActualNoNecessaryPartsHaveCausesAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → NoNecessaryPartsAt m w x → ∃ c, m.Causes w c x

/-- Both actual endpoints of the existing primitive cause relation at w. -/
def CausesHaveActualEndpointsAt {W B : Type} (m : Ontic W B) (w : W) : Prop :=
  ∀ c x, m.Causes w c x → m.ExistsAt w c ∧ m.ExistsAt w x

/-- OPEN nonoverlap of cause and effect; numerical distinction is insufficient.
Overlap retains the existing common-part meaning in the SAME fixed order. -/
def CauseEffectNonoverlapAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) : Prop :=
  ∀ c x, m.Causes w c x → ¬ Overlap c x

/-- Scoped reductio assumption ONLY, not an additional advertised premise. -/
def NoNecessaryBeingAt {W B : Type} (m : Ontic W B) (w : W) : Prop :=
  ¬ NecessaryBeing m w

/-- Selected type-fusion formation only when the actual no-necessary-parts
family is nonempty. No unrestricted all-Set fusion or unconditional actual sum
is asserted. The variant keeps actual population as a separate input. -/
def ConditionalActualFusionAt {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) : Prop :=
  (ActualNoNecessaryPartsFamily m w).Nonempty → ∃ sum, ActualFusionAt m w sum

end TruthCore.Causality.ActualFusionNecessaryBeing
