module

public import TruthCore.Explanation.ExistencePSR

/-!
Analyst comparison for the necessary-being route (#1595): an existence fact's
being essential to its bearer, a candidate intrinsic explanation of that fact,
and modal co-existence are three distinct typed claims.

`InEssence x (.fact y)` is an expressly primitive *source-indexed* nature
claim: the existence of `y` belongs to the nature of `x`. It is not defined
as `NecessaryAt`, modal co-presence, an efficient cause, or a grounded fact.
The existing `Reason.intrinsic` is only a candidate explanation token; the
models do not certify philosophical explanatory adequacy. The controls below
establish logical non-entailments for these selected meanings, not the
metaphysical possibility of the interpretations.

`InEssence` does not reuse `ExistenceIngredient.essential b`: that is only a
label naming an essential-existence fact inside a ground record, with no
bearer whose nature includes it. Here the bearer index is the point, since
`EssenceRequiresExistence p x y` may hold for `x ≠ y`. No bridge between the
two is encoded; reading `OwnEssentialExistence p x` as "the labelled fact
`essential x` obtains" would be a separate, open identification.

`OwnEssentialExistence` (essence membership) and `CandidateIntrinsicReason`
(an intrinsic explanation token) are distinct registered senses of
NECESSARY_EXISTENCE_BY_OWN_NATURE; passing from the first to the second is an
open bridge, not a definition.
-/

@[expose] public section

namespace TruthCore.Explanation.EssenceReasonSeparation

open TruthCore.Explanation.ExistencePSR
open TruthCore.German.Kant.CosmologicalInference

/-- Existing existence-fact explanation plus the nature-indexed facts of a
bearer. Nature membership is primitive, with its metaphysical interpretation
and essence-to-modality bridge left explicit and open. -/
structure Profile (World Being : Type) where
  explanation : Model World Being
  InEssence : Being → ExistenceFact Being → Prop

/-- Existence is represented among the facts in the bearer's own essence.
This is not the trivially true modal conditional `Exists(x) → Exists(x)`. -/
def OwnEssentialExistence (p : Profile W B) (x : B) : Prop :=
  p.InEssence x (.fact x)

/-- The nature of x requires the existence of y, as a source-indexed claim.
It has no converse-by-definition and need not be an asymmetric order. -/
def EssenceRequiresExistence (p : Profile W B) (x y : B) : Prop :=
  p.InEssence x (.fact y)

/-- An existing candidate noncausal reason token explains the existence fact.
The token's tag does not prove actual adequacy of the bearer's essence. -/
def CandidateIntrinsicReason (p : Profile W B) (w : W) (x : B) : Prop :=
  p.explanation.explains w (.intrinsic x) (.fact x)

/-- Mere necessity of co-existence, unable to distinguish the source of the
requirement when the right-hand being is necessary. -/
def ModalRequiresExistence (p : Profile W B) (w : W) (x y : B) : Prop :=
  ∀ v, p.explanation.ontic.frame.access w v →
    p.explanation.ontic.ExistsAt v x → p.explanation.ontic.ExistsAt v y

/-- Any necessarily existing y makes x's modal requirement of y automatic.
This fact alone says nothing about essence-indexed or explanatory dependence. -/
theorem modal_requirement_of_necessary (p : Profile W B) (w : W) (x y : B)
    (hy : NecessaryAt p.explanation.ontic w y) :
    ModalRequiresExistence p w x y := by
  intro v hv _
  exact hy v hv

/-- Fixed finite frame: both beings exist everywhere and no efficient causal
edge exists. Existence facts and candidate explanations remain distinct. -/
def alwaysExists : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

/-- Existence is essential to false, but no reason token explains anything. -/
def natureWithoutReason : Profile Bool Bool where
  explanation := { ontic := alwaysExists, explains := fun _ _ _ => False }
  InEssence := fun x fact => x = false ∧ fact = .fact false

/-- Candidate intrinsic reasons exist for true existence facts, but no
existence fact is represented as belonging to a bearer's essence. -/
def reasonWithoutNature : Profile Bool Bool where
  explanation := { ontic := alwaysExists, explains := fun _ _ _ => True }
  InEssence := fun _ _ => False

/-- The essence of false requires true; the essence of true does not require
false. Nevertheless both beings exist necessarily, so their mere modal
requirements hold symmetrically. -/
def directedNature : Profile Bool Bool where
  explanation := { ontic := alwaysExists, explains := fun _ _ _ => False }
  InEssence := fun x fact => x = false ∧ fact = .fact true

/-- Two actual necessary beings test each direction of the proposed
essential-existence ↔ intrinsic-explanation identification, and a third model
separates source-indexed existential dependence from symmetric necessary
co-existence. Explanation assignments are sound in the limited sense that
they explain only true existence facts; no model asserts adequacy of an
intrinsic nature-reason or general metaphysical possibility. -/
def SeparationControls : Prop :=
  (∃ p : Profile Bool Bool,
    Sound p.explanation ∧
    p.explanation.ontic.ExistsAt false false ∧
    NecessaryAt p.explanation.ontic false false ∧
    OwnEssentialExistence p false ∧
    ¬ CandidateIntrinsicReason p false false) ∧
  (∃ p : Profile Bool Bool,
    Sound p.explanation ∧
    p.explanation.ontic.ExistsAt false false ∧
    NecessaryAt p.explanation.ontic false false ∧
    ¬ OwnEssentialExistence p false ∧
    CandidateIntrinsicReason p false false) ∧
  (∃ p : Profile Bool Bool,
    Sound p.explanation ∧
    NecessaryAt p.explanation.ontic false false ∧
    NecessaryAt p.explanation.ontic false true ∧
    ModalRequiresExistence p false false true ∧
    ModalRequiresExistence p false true false ∧
    EssenceRequiresExistence p false true ∧
    ¬ EssenceRequiresExistence p true false ∧
    ¬ p.explanation.ontic.Causes false false true ∧
    ¬ p.explanation.ontic.Causes false true false)

/-! ### The existence-PSR context of the target bridge

The first control has no explanations at all, so it violates `ExistencePSR`.
The two facts below are not registered results; they record where the
candidate token comes from once the PSR context of the necessary-ground
target is restored. -/

/-- Control (1) with `ExistencePSR` restored: every existence fact has only a
circumstance token, so essence membership still holds without a candidate
intrinsic reason. -/
def natureWithCircumstanceReason : Profile Bool Bool where
  explanation :=
    { ontic := alwaysExists, explains := fun _ r _ => r = .circumstance true }
  InEssence := fun x fact => x = false ∧ fact = .fact false

/-- Restoring `ExistencePSR` keeps `B ∧ ¬CandidateC` satisfiable. -/
theorem psr_keeps_nature_without_intrinsic_reason :
    Sound natureWithCircumstanceReason.explanation ∧
    ExistencePSR natureWithCircumstanceReason.explanation ∧
    NecessaryAt natureWithCircumstanceReason.explanation.ontic false false ∧
    OwnEssentialExistence natureWithCircumstanceReason false ∧
    ¬ CandidateIntrinsicReason natureWithCircumstanceReason false false := by
  refine ⟨fun _ _ _ _ => trivial, fun _ _ _ => ⟨.circumstance true, rfl⟩,
    fun _ _ => trivial, ⟨rfl, rfl⟩, ?_⟩
  intro h
  cases h

/-- Under `ExistencePSR`, an existent whose existence fact is explained by no
circumstance token and by no other being's intrinsic token is explained by its
own intrinsic token. Essence membership is not used: the candidate token comes
from the PSR and the exclusions, whether or not `OwnEssentialExistence` holds.
Its adequacy as an explanation remains open. -/
theorem candidate_intrinsic_of_psr_without_other_reasons (p : Profile W B)
    (hpsr : ExistencePSR p.explanation) (w : W) (x : B)
    (hx : p.explanation.ontic.ExistsAt w x)
    (hnoCirc : ∀ y, ¬ p.explanation.explains w (.circumstance y) (.fact x))
    (hbearer : ∀ y, p.explanation.explains w (.intrinsic y) (.fact x) → y = x) :
    CandidateIntrinsicReason p w x := by
  obtain ⟨r, hr⟩ := hpsr w x hx
  cases r with
  | circumstance y => exact absurd hr (hnoCirc y)
  | intrinsic y =>
    have hy := hbearer y hr
    subst hy
    exact hr

end TruthCore.Explanation.EssenceReasonSeparation
