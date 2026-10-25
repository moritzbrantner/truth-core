import TruthCore.Logic.ExcludedMiddle
import TruthCore.Modern.Hume.Conceivability

/-! Stipulated mathematical semantics for #261; no source attribution.
Domains do not assert which propositions describe metaphysical possibilities. -/
namespace TruthCore.Modal.ResearchFixture
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box)
open TruthCore.Modern.Hume.Conceivability (Collapse)
universe u v
variable {W : Type u}

/-- An explicit admissibility predicate, with no comprehension assumed. -/
abbrev Domain (W : Type u) := MProp W → Prop

def allPredicates : Domain W := fun _ => True

/-- Scope (b): exactly the denotations of formulas in this fixed language/model. -/
def expressible {A : Type v} (F : Frame W) (V : Valuation W A) : Domain W :=
  fun P => ∃ φ : Formula A, P = fun w => Holds F V w φ

/-- Scope (c): only the explicitly supplied corpus inventory, not all formulas. -/
def corpusDomain {I : Type v} (inventory : I → MProp W) : Domain W :=
  fun P => ∃ i, P = inventory i

/-- Root-relative modal collapse; quantification is restricted to D. -/
def MC (F : Frame W) (D : Domain W) (w : W) : Prop :=
  ∀ P, D P → P w → Box F P w

/-- Identity predicates are admissible only when this condition is supplied. -/
def IdentityAdmissible (D : Domain W) (w : W) : Prop := D (fun v => v = w)

/-- Agreement at all propositions in D, independently of accessibility. -/
def Agree (D : Domain W) (w v : W) : Prop := ∀ P, D P → (P w ↔ P v)

/-- Owner-requested identity criterion, separate from modal collapse and Lean propext.
Whether D contains complete propositions is an additional interpretive commitment. -/
def PropositionalExtensionality (D : Domain W) : Prop :=
  ∀ w v, Agree D w v → w = v

/-- Exact assumption: only root identity-predicate admissibility is needed. -/
theorem identity_separates (F : Frame W) (D : Domain W) (w : W)
    (hIdentity : IdentityAdmissible D w) (hMC : MC F D w) :
    ∀ v, F.access w v → v = w := by
  intro v hv
  exact hMC (fun x => x = w) hIdentity rfl v hv

/-- No frame conditions or world extensionality are needed for this equivalence. -/
theorem full_iff_hume (F : Frame W) (w : W) :
    MC F allPredicates w ↔ Collapse F w := by
  constructor
  · intro h P; exact h P trivial
  · intro h P _; exact h P

/-- Shrinking a domain preserves collapse; enlarging it need not. -/
theorem restrict (F : Frame W) (D E : Domain W) (w : W)
    (hSub : ∀ P, E P → D P) (h : MC F D w) : MC F E w := by
  intro P hp; exact h P (hSub P hp)

/-- Negation closure is explicit: one-way persistence then gives agreement. -/
theorem collapse_agreement (F : Frame W) (D : Domain W) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hNeg : ∀ P, D P → D (fun v => ¬ P v)) (hMC : MC F D w) :
    ∀ v, F.access w v → Agree D w v := by
  intro v hv P hp
  constructor
  · intro h; exact hMC P hp h v hv
  · intro h
    cases hEM (P w) with
    | inl hw => exact hw
    | inr hn => exact (hMC (fun x => ¬ P x) (hNeg P hp) hn v hv h).elim

/-- This route to identity uses extensionality and negation closure, unlike separation. -/
theorem extensional_separates (F : Frame W) (D : Domain W) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hNeg : ∀ P, D P → D (fun v => ¬ P v))
    (hExt : PropositionalExtensionality D) (hMC : MC F D w) :
    ∀ v, F.access w v → w = v := by
  intro v hv
  exact hExt w v (collapse_agreement F D w hEM hNeg hMC v hv)

/-- Bundled contract: all mathematical assumptions stay inside the quantified laws. -/
def Checks : Prop :=
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    IdentityAdmissible D w → MC F D w → ∀ v, F.access w v → v = w) ∧
  (∀ (W : Type) (F : Frame W) w, MC F allPredicates w ↔ Collapse F w) ∧
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    (TruthCore.Logic.ExcludedMiddle) →
    (∀ P, D P → D (fun v => ¬ P v)) → PropositionalExtensionality D →
    MC F D w → ∀ v, F.access w v → w = v)
end TruthCore.Modal.ResearchFixture
