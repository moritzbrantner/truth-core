module

public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Mereology.SupplementationFusion

/-!
Analyst structural survivor for #331/#1097, attribution deferred. One rigid
whole exists at both alternative worlds, with two disjoint actual proper parts
at EACH world; the two pairs differ. Worlds are alternatives, not successive
times. The same whole-first support relation supplies P2 and P3. It is not
inferred from containment or claimed intrinsically adequate.

Each actual-domain subtype inherits the existing nonempty-subsets-of-Bool
parthood via an injective representation. Overlap, Sum2 fusion and strong
supplementation retain their existing meanings. Actual parthood guards BOTH
endpoints; no fixed whole-roster parthood or modal part-persistence is assumed.
The whole's primitive necessity, concrete classification and support are model
assignments, not a real-world argument. See docs/notes/worldwise-composite-ground.md
for the rejected three-object candidate and the revised semantic scope.
-/

@[expose] public section
namespace TruthCore.Causality.WorldwiseCompositeGround
open BruteFoundationBoundary CausalPowerConcreteness
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Mereology

inductive Body | whole | atom (cohort slot : Bool) deriving DecidableEq

def existsAt (w : Bool) : Body → Prop
  | .whole => True
  | .atom cohort _ => cohort = w

/-- Same direct relation in the cause and support fields. Both active parts
are supported by the whole; neither is declared to support its whole. -/
def support (w : Bool) (c x : Body) : Prop :=
  c = .whole ∧ ∃ slot, x = .atom w slot

def profile : Profile Bool Body where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := existsAt
    Causes := support }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding/modal structure, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := support

/-- Ordered objects at this world are actual, not absent self-parts. -/
abbrev Actual (w : Bool) := {x : Body // existsAt w x}

/-- Local nonempty material representation; cohorts distinguish rigid global
candidates, while slot distinguishes the two disjoint local atoms. -/
def content : Body → UniversalFusionBoundary.Body
  | .whole => UniversalFusionBoundary.whole
  | .atom _ slot => UniversalFusionBoundary.atom slot

theorem whole_ne_atom (b : Bool) : UniversalFusionBoundary.whole ≠ UniversalFusionBoundary.atom b := by
  intro h
  have hm : (!b) ∈ UniversalFusionBoundary.whole.val := True.intro
  rw [h] at hm
  change (!b) = b at hm
  cases b <;> cases hm

theorem atom_inj (a b : Bool) (h : UniversalFusionBoundary.atom a = UniversalFusionBoundary.atom b) : a = b := by
  have hm : a ∈ (UniversalFusionBoundary.atom a).val := rfl
  rw [h] at hm
  exact hm

theorem content_injective (w : Bool) :
    Function.Injective (fun x : Actual w => content x.val) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply Subtype.ext
  cases x with
  | whole =>
    cases y with
    | whole => rfl
    | atom c b => exact False.elim (whole_ne_atom b h)
  | atom c a =>
    cases y with
    | whole => exact False.elim (whole_ne_atom a h.symm)
    | atom d b =>
      have hab := atom_inj a b h
      change c = w at hx
      change d = w at hy
      cases hx
      cases hy
      cases hab
      rfl

/-- Existing subset parthood on the indexed actual domain, not a new
mereological relation or a fixed order on every global candidate. -/
instance (w : Bool) : PartialOrder (Actual w) :=
  PartialOrder.lift (fun x => content x.val) (content_injective w)

def wholeAt (w : Bool) : Actual w := ⟨.whole, True.intro⟩
def atomAt (w slot : Bool) : Actual w := ⟨.atom w slot, rfl⟩

def actualPart (w : Bool) (x y : Body) : Prop :=
  existsAt w x ∧ existsAt w y ∧ content x ≤ content y

def actualProperPart (w : Bool) (x y : Body) : Prop := actualPart w x y ∧ x ≠ y

def pair (w : Bool) : Set (Actual w) := {atomAt w false, atomAt w true}

/-- One same-profile strengthened survivor. No NE inference or numerical unity
argument is advertised. All parthood/overlap quantifiers below use actual
objects at their indexed world, with no empty/null object added. -/
def ReplacementCertificate : Prop :=
  (∃ p : IntendedProfile Bool Body,
    p.underlying = profile ∧ (∀ x, ¬ p.abstract x) ∧
    (∀ w x, p.hasCausalPower w x ↔ x = .whole) ∧
    (∀ w, P2At p w ∧ P3At p w)) ∧
  (∀ w, profile.concrete .whole ∧ existsAt w .whole ∧
    NecessaryAt profile.ontic w .whole) ∧
  (∀ w slot, actualProperPart w (.atom w slot) .whole ∧
    ContingentAt profile.ontic w (.atom w slot) ∧
    profile.grounds w .whole (.atom w slot)) ∧
  (∀ w, TruthCore.Mereology.SupplementationFusion.StrongSupplementation (Actual w) ∧
    UniversalFusionBoundary.Fusion (pair w) (wholeAt w) ∧
    ¬ UniversalFusionBoundary.Overlap (atomAt w false) (atomAt w true)) ∧
  (∀ w (x y : Actual w), x ≤ y ↔ actualPart w x.val y.val) ∧
  (¬ ∃ x, (∃ w, actualProperPart w x .whole) ∧
    NecessaryAt profile.ontic false x) ∧
  (¬ ∃ x, ∀ w, actualProperPart w x .whole) ∧
  (∀ w x, actualProperPart w x .whole → ¬ profile.grounds w x .whole)

end TruthCore.Causality.WorldwiseCompositeGround
