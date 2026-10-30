import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Models.FiniteSupport

/-! #438: two relations on candidate descriptions, reusing Frame and Box/Dia.
The carrier is NOT asserted to consist entirely of metaphysically possible
states. Only M-accessible descriptions are admitted by the stipulated stronger
profile. Neither relation describes proof search or actual human knowledge.
No historical claim or syntactic consistency theorem is made here. -/
namespace TruthCore.Modal.PossibilityTransfer
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)

/-- Pointwise inclusion at the selected origin; not assumed as a modal axiom. -/
def IncludedAt {D : Type} (E M : Frame D) (w : D) : Prop :=
  ∀ v, E.access w v → M.access w v

/-- Universal predicate quantification is essential: singleton predicates are
available, unlike a restricted conceptual vocabulary. -/
def TransferLaws : Prop :=
  (∀ (D : Type) (E M : Frame D) w,
    (∀ P : MProp D, Dia E P w → Dia M P w) ↔ IncludedAt E M w) ∧
  (∀ (D : Type) (E M : Frame D) w,
    (∀ P : MProp D, Box M P w → Box E P w) ↔ IncludedAt E M w)

/-- Coarse admissibility: both descriptions remain epistemic alternatives. -/
def epistemic : Frame Bool := ⟨fun _ _ => True⟩
/-- Stronger stipulated profile: only the origin's own description is admitted.
This is a model-relative filter, not a definition of real metaphysical truth. -/
def metaphysical : Frame Bool := ⟨fun w v => v = w⟩
/-- A satisfiable description; its true witness need not be M-admissible at false. -/
def description : MProp Bool := fun v => v = true

/-- Both relations are equivalences (hence serial); the separation is not an
empty-accessibility artifact. The inclusion M ⊆ E holds, the converse fails.
P has an explicit satisfying candidate and E-witness but no M-witness at false;
M-box-not-P holds whereas E-box-not-P fails. This omits precisely E ⊆ M. -/
def OmissionControl : Prop :=
  Reflexive epistemic ∧ Symmetric epistemic ∧ Transitive epistemic ∧
  Reflexive metaphysical ∧ Symmetric metaphysical ∧ Transitive metaphysical ∧
  (∀ w, IncludedAt metaphysical epistemic w) ∧
  (¬ IncludedAt epistemic metaphysical false) ∧
  description true ∧ Dia epistemic description false ∧
  (¬ Dia metaphysical description false) ∧
  Box metaphysical (fun v => ¬ description v) false ∧
  (¬ Box epistemic (fun v => ¬ description v) false)

/-- Exact two-relation transfer laws and a concrete omitted-inclusion control.
Internal universally quantified profiles are not established world hypotheses. -/
def Checks : Prop := TransferLaws ∧ OmissionControl
end TruthCore.Modal.PossibilityTransfer
