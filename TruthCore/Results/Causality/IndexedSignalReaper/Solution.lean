import TruthCore.Causality.IndexedSignalReaper
import TruthCore.Results.Causality.IndexedSignalProvenance.Solution
import TruthCore.Results.Causality.GrimReaperImpossible.Solution

namespace TruthCore.Results.Causality.IndexedSignalReaper
open TruthCore.Causality
open TruthCore.Causality.IndexedSignalProvenance
open TruthCore.Causality.IndexedSignalReaper

/-- The three response interfaces derive conservation, rather than assuming
a global originating event or the earlier conservation interface afresh. -/
theorem localConservation (signal : Nat → Option Nat) (issued : Nat → Prop)
    (hTrigger : PositiveTrigger signal issued) (hEmit : Emission signal issued)
    (hForward : Forwarding signal) : LocalConservation signal issued := by
  intro n j hs
  cases hInput : signal (n + 1) with
  | none =>
    have hi := hTrigger n hInput
    have hj := Option.some.inj (hs.symm.trans (hEmit n hi))
    exact Or.inl ⟨hi, hj⟩
  | some k =>
    have hj := Option.some.inj (hs.symm.trans (hForward n k hInput))
    cases hj
    exact Or.inr rfl

/-- Preserve one fixed code over any finite upstream interval. -/
theorem forwardSteps (signal : Nat → Option Nat) (hForward : Forwarding signal)
    (n m j : Nat) (hnm : n ≤ m) (hs : signal m = some j) : signal n = some j := by
  induction hnm with
  | refl => exact hs
  | @step m _ ih => exact ih (hForward m j hs)

/-- Derive the existing action law from four explicit local interfaces;
neither global provenance nor the action law is an input. -/
theorem firingLaw (signal : Nat → Option Nat) (issued : Nat → Prop)
    (hBound : IndexAdmissible signal)
    (hTrigger : PositiveTrigger signal issued)
    (hEmit : Emission signal issued)
    (hForward : Forwarding signal) : GrimReaperLaw issued := by
  have hOrigin := TruthCore.Results.Causality.IndexedSignalProvenance.provenance
    signal issued (localConservation signal issued hTrigger hEmit hForward) hBound
  intro n
  constructor
  · intro hn m hnm hm
    have hmAt := forwardSteps signal hForward n m m (Nat.le_of_lt hnm) (hEmit m hm)
    have heq := Option.some.inj ((hEmit n hn).symm.trans hmAt)
    exact Nat.ne_of_lt hnm heq
  · intro hNone
    cases hInput : signal (n + 1) with
    | none => exact hTrigger n hInput
    | some j =>
      have hj := hOrigin (n + 1) j hInput
      have hnj := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (hBound (n + 1) j hInput)
      exact (hNone j hnj hj).elim

/-- Composition with the original impossibility certifies an incompatible
four-rule bundle, not a satisfiable actual or possible signaling system. -/
theorem impossible (signal : Nat → Option Nat) (issued : Nat → Prop)
    (hBound : IndexAdmissible signal) (hTrigger : PositiveTrigger signal issued)
    (hEmit : Emission signal issued) (hForward : Forwarding signal) : False :=
  TruthCore.Results.Causality.GrimReaperImpossible.grimReaperImpossible
    ⟨issued, firingLaw signal issued hBound hTrigger hEmit hForward⟩

/-- Four same-carrier omissions retain all three other local rules. -/
theorem controls : TruthCore.Causality.IndexedSignalReaper.Controls := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun _ => some 0, fun _ => False, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ h
      cases h
    · intro _ h
      exact h.elim
    · intro _ _ h
      exact h
    · intro h
      exact Nat.not_succ_le_zero 0 (h 1 0 rfl)
    · intro h
      exact (h 0).mpr (fun _ _ hi => hi)
  · refine ⟨fun _ => none, fun _ => False, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ h
      cases h
    · intro _ h
      exact h.elim
    · intro _ _ h
      cases h
    · intro h
      exact h 0 rfl
    · intro h
      exact (h 0).mpr (fun _ _ hi => hi)
  · refine ⟨fun _ => none, fun _ => True, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ h
      cases h
    · intro _ _
      trivial
    · intro _ _ h
      cases h
    · intro h
      have hn := h 0 True.intro
      cases hn
    · intro h
      exact (h 0).mp True.intro 1 (Nat.lt_succ_self 0) True.intro
  · refine ⟨fun n => some n, fun _ => True, ?_, ?_, ?_, ?_, ?_⟩
    · intro n j hs
      cases hs
      exact Nat.le_refl n
    · intro _ h
      cases h
    · intro _ _
      rfl
    · intro h
      have hn := h 0 1 rfl
      cases hn
    · intro h
      exact (h 0).mp True.intro 1 (Nat.lt_succ_self 0) True.intro

end TruthCore.Results.Causality.IndexedSignalReaper
