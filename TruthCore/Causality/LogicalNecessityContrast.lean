module

public import TruthCore.Causality.NecessarySenseFork

/-!
Analyst contrast for NECESSARY_5, not a completed binding of that generic
sense. This selected profile is classical propositional modal semantics on
one explicitly supplied frame, with ALL valuations and ALL its worlds admitted.
It serves the omitted logical-necessity branch of NecessarySenseFork. The
frame is not claimed to exhaust every logic or interpretation of existence.
-/
@[expose] public section

namespace TruthCore.Causality.LogicalNecessityContrast

open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork

/-- In this explicit frame profile, denial is contradictory precisely when
no valuation/world interpretation satisfies the syntactic denial. This body
quantifies the entire admitted interpretation domain, not one actual model.
An empty world carrier makes this vacuous; controls below use Unit. -/
def DenialContradictory {W A : Type} (F : Frame W) (φ : Formula A) : Prop :=
  ¬ ∃ (V : Valuation W A) (w : W), Holds F V w (Formula.neg φ)

/-- Classical semantic contradiction of denial is frame validity. This is
semantic unsatisfiability, not syntactic derivability or a completeness claim. -/
theorem denialContradictory_iff_valid {W A : Type} (F : Frame W) (φ : Formula A) :
    DenialContradictory F φ ↔ Valid F φ := by
  classical
  constructor
  · intro h V w
    by_contra hn
    exact h ⟨V, w, hn⟩
  · intro h ⟨V, w, hn⟩
    exact hn (h V w)

/-- Validity implies truth and box-truth in any selected interpretation of
THIS SAME formula on THIS SAME frame, without a reflexivity premise. -/
theorem valid_truth_and_box {W A : Type} (F : Frame W) (φ : Formula A)
    (h : Valid F φ) (V : Valuation W A) (w : W) :
    Holds F V w φ ∧ Holds F V w (.box φ) :=
  ⟨h V w, fun v _ => h V v⟩

/-- On every inhabited carrier an unconstrained atom fails frame validity:
the everywhere-false valuation is admitted, regardless of frame laws. -/
theorem atom_not_valid {W A : Type} [Nonempty W] (F : Frame W) (a : A) :
    ¬ Valid F (.atom a) := by
  intro h
  obtain ⟨w⟩ := ‹Nonempty W›
  exact h (fun _ _ => False) w

/-- Positive nonvacuity: implication identity is valid and has contradictory
denial in the very same inhabited Unit frame used for the negative control. -/
theorem identity_denial_contradictory :
    DenialContradictory Control.unitProfile.ontic.frame
      (.imp (.atom ()) (.atom ())) := by
  apply (denialContradictory_iff_valid _ _).mpr
  intro V w h
  exact h

/-- Even in the route's populated reflexive universal one-world frame (S5),
actual truth and box-existence of the fixed candidate do not give logical
validity of its existence atom. No God conclusion is inferred. -/
theorem route_existence_not_valid :
    Holds Control.unitProfile.ontic.frame
      (existenceValuation Control.unitProfile.ontic) () (.atom ()) ∧
    BoxExistsAt Control.unitProfile.ontic () () ∧
    ¬ DenialContradictory Control.unitProfile.ontic.frame (.atom ()) := by
  refine ⟨True.intro, ?_, ?_⟩
  · intro v _
    trivial
  · intro h
    exact atom_not_valid _ () ((denialContradictory_iff_valid _ _).mp h)

end TruthCore.Causality.LogicalNecessityContrast
