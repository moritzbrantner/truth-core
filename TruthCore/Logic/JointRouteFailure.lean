module

public import TruthCore.Logic.ExcludedMiddle

/-!
# Joint failure of routes (#1119)

An indexed route is the conjunction of all its premises; its failure has a
missing premise. A consequence of one selected failure mode does not cover
failure of the route. The pattern below requires every mode to have the stated
consequence. With incompatible consequences, at least one route holds.

This is a logical rule template over opaque proposition families, not a
philosophical argument or a certificate for any concrete pair of root routes.
Instantiations must provide the two complete route derivations, exhaustive
failure consequences and their incompatibility under one semantic profile.
Nothing here establishes those inputs. No external classical axiom is used:
excluded middle is an explicit parameter, as on the existing root routes.
-/

@[expose] public section

namespace TruthCore.Logic.JointRouteFailure

/-- All premises of an indexed route hold. Empty routes are true. -/
def Complete {I : Type} (premises : I → Prop) : Prop := ∀ i, premises i

/-- Some premise of the route fails. -/
def Failure {I : Type} (premises : I → Prop) : Prop := ∃ i, ¬ premises i

/-- The consequence follows for every possible failed premise, not just a
selected witness. This makes the exhaustive failure-mode obligation explicit. -/
def EveryFailureEntails {I : Type} (premises : I → Prop) (consequence : Prop) : Prop :=
  ∀ i, ¬ premises i → consequence

/-- A failed premise rules out completion, constructively. -/
theorem failure_not_complete {I : Type} (premises : I → Prop)
    (h : Failure premises) : ¬ Complete premises := by
  obtain ⟨i, hi⟩ := h
  intro hAll
  exact hi (hAll i)

/-- The converse needs a decision principle; excluded middle is explicit. -/
theorem failure_of_not_complete {I : Type} (premises : I → Prop)
    (hEM : ExcludedMiddle) (hNot : ¬ Complete premises) : Failure premises := by
  cases hEM (Failure premises) with
  | inl h => exact h
  | inr hNone =>
    have hAll : Complete premises := by
      intro i
      cases hEM (premises i) with
      | inl hi => exact hi
      | inr hi => exact False.elim (hNone ⟨i, hi⟩)
    exact False.elim (hNot hAll)

/-- Coverage from incompatibility of exhaustive failure consequences. -/
theorem coverage {I J : Type} (left : I → Prop) (right : J → Prop)
    (X Y : Prop) (hEM : ExcludedMiddle)
    (hLeft : EveryFailureEntails left X)
    (hRight : EveryFailureEntails right Y)
    (hIncompatible : ¬ (X ∧ Y)) : Complete left ∨ Complete right := by
  cases hEM (Complete left) with
  | inl h => exact Or.inl h
  | inr hNotLeft =>
    have hX : X := by
      obtain ⟨i, hi⟩ := failure_of_not_complete left hEM hNotLeft
      exact hLeft i hi
    apply Or.inr
    intro j
    cases hEM (right j) with
    | inl hj => exact hj
    | inr hj => exact False.elim (hIncompatible ⟨hX, hRight j hj⟩)

/-- The requested logical pattern. It supplies no particular philosophical
premise family or route certificate; callers must instantiate every input. -/
def RootFromJointFailureIncompatibility : Prop :=
  ∀ (I J : Type) (left : I → Prop) (right : J → Prop) (root X Y : Prop),
    (Complete left → root) → (Complete right → root) →
    EveryFailureEntails left X → EveryFailureEntails right Y →
    ¬ (X ∧ Y) → root

/-- At least one complete route suffices for the common conclusion. -/
theorem rootFromJointFailureIncompatibility (hEM : ExcludedMiddle) :
    RootFromJointFailureIncompatibility := by
  intro I J left right root X Y hRouteLeft hRouteRight hLeft hRight hIncompatible
  cases coverage left right X Y hEM hLeft hRight hIncompatible with
  | inl h => exact hRouteLeft h
  | inr h => exact hRouteRight h

/-- If both routes require a shared obligation, covering them still requires
that obligation. Cross-route composition cannot evade shared leaves. -/
theorem shared_obligation {I J : Type} (left : I → Prop) (right : J → Prop)
    (common : Prop) (hLeft : Complete left → common)
    (hRight : Complete right → common)
    (hCoverage : Complete left ∨ Complete right) : common := by
  cases hCoverage with
  | inl h => exact hLeft h
  | inr h => exact hRight h

/-- A finite control: a route has one true and one false premise. A selected true premise has an impossible failure, so one sampled
failure implication can hold with a false consequence even though both routes
fail. Thus existential sampling cannot replace EveryFailureEntails. -/
def SampledFailureControl : Prop :=
  let premises : Bool → Prop := fun b => b = true
  ¬ Complete premises ∧ Failure premises ∧
  (∃ i, ¬ premises i → False) ∧ ¬ EveryFailureEntails premises False

theorem sampledFailureControl : SampledFailureControl := by
  dsimp [SampledFailureControl]
  have hFalse : ¬ (false = true) := by intro h; cases h
  refine ⟨?_, ⟨false, hFalse⟩, ⟨true, ?_⟩, ?_⟩
  · intro hAll
    exact hFalse (hAll false)
  · intro h
    exact h rfl
  · intro hEvery
    exact hEvery false hFalse

end TruthCore.Logic.JointRouteFailure
