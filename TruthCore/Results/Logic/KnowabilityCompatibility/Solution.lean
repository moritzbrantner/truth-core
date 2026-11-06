module

public import TruthCore.Logic.KnowabilityCompatibility
public import TruthCore.Results.Logic.FitchKnowability.Solution

@[expose] public section

namespace TruthCore.Results.Logic.KnowabilityCompatibility
open TruthCore.Modal TruthCore.Logic.FitchKnowability
open TruthCore.Logic.KnowabilityCompatibility

/-- Euclidean sibling reach and reverse knowability force admitted knowledge.
No epistemic factivity, modal reflexivity or Moore closure is a premise. -/
theorem admittedKnown {W : Type} (E R : Frame W) (actual : W)
    (C : (W → Prop) → Prop) (euclidean : Euclidean R)
    (included : Included E R)
    (equivalence : GlobalRestrictedEquivalence (relationalContext E R actual) C) :
    AdmittedKnown (relationalContext E R actual) C := by
  intro p admissible w truth u epistemic
  obtain ⟨v, modal, known⟩ := (equivalence p admissible w).mp truth
  exact (equivalence p admissible u).mpr
    ⟨v, euclidean w u v (included w u epistemic) modal, known⟩

local instance : NeZero 4 := ⟨Nat.noConfusion⟩

private abbrev E := survivorEpistemic
private abbrev C := AtomInvariant survivorAtom

/-- Extend only the modal witness relation; contents, agent and K are fixed. -/
private theorem extendForward (R : Frame (Fin 4))
    (extension : Included survivorModal R)
    (equivalence : GlobalRestrictedEquivalence survivorContext C) :
    GlobalForward (relationalContext E R 0) C := by
  intro p admissible w truth
  obtain ⟨v, access, known⟩ := (equivalence p admissible w).mp truth
  exact ⟨v, extension w v access, known⟩

private theorem universalEuclidean : Euclidean universalModal :=
  fun _ _ _ _ _ => True.intro

/-- The forward survivor imports the complete old epistemic/content checks;
only modal accessibility changes. Reverse knowability would contradict the
already checked actual ignorance through admittedKnown. -/
theorem forwardSurvivor : ForwardSurvivor := by
  rcases TruthCore.Results.Logic.FitchKnowability.restrictedSurvivor with
    ⟨_, er, es, et, _, _, _, laws, closed, atom, equivalence, unknown, inadmissible, _⟩
  refine ⟨er, es, et, (fun _ => True.intro), (fun _ _ _ => True.intro),
    (fun _ _ _ _ _ => True.intro), universalEuclidean,
    (fun _ _ _ => True.intro), laws, closed, atom,
    extendForward universalModal (fun _ _ _ => True.intro) equivalence,
    unknown, ?_, inadmissible⟩
  intro stronger
  exact unknown.2
    (admittedKnown E universalModal 0 C universalEuclidean
      (fun _ _ _ => True.intro) stronger survivorAtom atom 0 unknown.1)

private theorem lineEquivalence
    (symmetry : Symmetric E)
    (equivalence : GlobalRestrictedEquivalence survivorContext C) :
    GlobalRestrictedEquivalence lineContext C := by
  intro p admissible w
  constructor
  · exact extendForward lineModal (fun _ _ h => Or.inr h) equivalence p admissible w
  · rintro ⟨v, access, known⟩
    rcases access with epistemic | modal
    · exact known w (symmetry w v epistemic)
    · exact (equivalence p admissible w).mpr ⟨v, modal, known⟩

private theorem lineNotEuclidean : ¬ Euclidean lineModal := by
  intro euclidean
  have edge01 : lineModal.access 0 1 :=
    Or.inl (Or.inl ⟨by decide, by decide⟩)
  have edge02 : lineModal.access 0 2 :=
    Or.inr ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl⟩
  have edge12 := euclidean 0 1 2 edge01 edge02
  rcases edge12 with epistemic | modal
  · rcases epistemic with ⟨_, impossible⟩ | impossible
    · exact Nat.not_lt_of_ge (Nat.le_refl 2) impossible
    · exact (by decide : (1 : Fin 4) ≠ 2) impossible
  · have notOne : ¬ survivorAtom 1 := by
      unfold survivorAtom
      decide
    exact notOne (modal.mpr (Or.inr rfl))

/-- The reflexive/symmetric union frame retains the biconditional while
rejecting Euclideanness. This is a frame-relative omission control, not a
claim that metaphysical possibility has this structure. -/
theorem lineSurvivor : LineSurvivor := by
  rcases TruthCore.Results.Logic.FitchKnowability.restrictedSurvivor with
    ⟨_, er, es, et, _, rs, _, laws, closed, atom, equivalence, unknown, inadmissible, _⟩
  refine ⟨er, es, et, (fun w => Or.inl (er w)), ?_, lineNotEuclidean,
    (fun _ _ h => Or.inl h), laws, closed, atom,
    lineEquivalence es equivalence, unknown, inadmissible⟩
  intro u v access
  rcases access with epistemic | modal
  · exact Or.inl (es u v epistemic)
  · exact Or.inr (rs u v modal)

/-- Same-world joint witness for the three collapse assumptions, with a
nonconstant admitted atom, rather than an inconsistent or empty background. -/
theorem positiveSurvivor : PositiveSurvivor := by
  rcases TruthCore.Results.Logic.FitchKnowability.restrictedSurvivor with
    ⟨_, _, _, _, _, rs, rt, _, closed, atom, _, _, _, _⟩
  have euclidean : Euclidean survivorModal :=
    symmetric_transitive_implies_euclidean survivorModal rs rt
  have included : Included survivorModal survivorModal := fun _ _ h => h
  have equivalence : GlobalRestrictedEquivalence positiveContext C := by
    intro p invariant w
    constructor
    · intro truth
      refine ⟨w, Iff.rfl, ?_⟩
      intro v access
      exact (invariant w v access).mp truth
    · rintro ⟨v, access, known⟩
      exact (invariant w v access).mpr (known v Iff.rfl)
  refine ⟨euclidean, included, closed, atom, equivalence,
    admittedKnown survivorModal survivorModal 0 C euclidean included equivalence,
    Or.inl rfl, ?_⟩
  unfold survivorAtom
  decide

end TruthCore.Results.Logic.KnowabilityCompatibility
