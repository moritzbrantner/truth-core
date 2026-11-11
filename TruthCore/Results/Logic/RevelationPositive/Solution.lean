module
public import TruthCore.Logic.RevelationPositive
public import TruthCore.Results.Logic.CorrectionCriterion.Solution
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

@[expose] public section
namespace TruthCore.Results.Logic.RevelationPositive
open TruthCore.Logic.RevelationPositive

theorem characterization : Characterization := by
  intro F g a
  constructor
  · rintro ⟨certify, sound, w₀, admitted, yes, authored⟩
    refine ⟨w₀, admitted, authored, ?_⟩
    intro w hw same
    exact sound w hw (same.symm ▸ yes)
  · rintro ⟨w₀, admitted, authored, pure⟩
    exact ⟨(fun e => e = F.observe a w₀), pure, w₀, admitted, rfl, authored⟩

private theorem fullInvariant (F : Frame) (g : F.Candidate) (a : F.Event)
    (h : FullClassifier F g a) :
    ∀ (s t : {w // F.admitted w}), F.observe a s.val = F.observe a t.val →
      (F.authored g a s.val ↔ F.authored g a t.val) :=
  (TruthCore.Results.Logic.CorrectionCriterion.characterization.1 _ _ _ _).mp h

private theorem noPositive (F : Frame) (g : F.Candidate) (a : F.Event)
    (bad : ∀ w, F.admitted w → F.authored g a w →
      ∃ v, F.admitted v ∧ F.observe a v = F.observe a w ∧ ¬ F.authored g a v) :
    ¬ SoundPositive F g a := by
  intro h
  obtain ⟨w, hw, ha, pure⟩ := (characterization F g a).mp h
  obtain ⟨v, hv, same, hn⟩ := bad w hw ha
  exact hn (pure v hv same)

theorem controls : Controls := by
  have amb : ¬ SoundPositive ambiguous () () := by
    apply noPositive
    intro w _ ha
    refine ⟨1, trivial, rfl, ?_⟩
    decide
  have imit : ¬ SoundPositive imitated () () := by
    apply noPositive
    intro w _ ha
    change Fin 4 at w
    refine ⟨(if w.val = 0 then 3 else 2), trivial, ?_, ?_⟩
    · fin_cases w <;> simp_all [imitated, finite]
    · fin_cases w <;> simp [discriminated, finite]
  have dist : SoundPositive distinctive () () := by
    apply (characterization _ _ _).mpr
    refine ⟨0, trivial, by decide, ?_⟩
    intro w _ same
    change Fin 3 at w
    fin_cases w <;> simp_all [distinctive, finite]
  have disc : FullClassifier discriminated () () := by
    refine ⟨(fun e => e = 1), ?_⟩
    intro w
    rcases w with ⟨w, _⟩
    change Fin 2 at w
    fin_cases w <;> simp [discriminated, finite]
  refine ⟨⟨amb, ?_⟩, ⟨dist, ?_⟩, ⟨?_, disc⟩, ⟨imit, ?_⟩⟩
  · intro h
    have bad := (fullInvariant _ _ _ h ⟨0, trivial⟩ ⟨1, trivial⟩ rfl).mp rfl
    cases bad
  · intro h
    have bad := (fullInvariant _ _ _ h ⟨1, trivial⟩ ⟨2, trivial⟩ rfl).mp (by decide)
    exact (by decide : ¬ (2 < 2)) bad
  · apply (characterization _ _ _).mpr
    refine ⟨0, trivial, rfl, ?_⟩
    intro w _ same
    change Fin 2 at w
    fin_cases w <;> simp_all [discriminated, finite]
  · intro h
    have bad := (fullInvariant _ _ _ h ⟨0, trivial⟩ ⟨3, trivial⟩ rfl).mp (by decide)
    exact (by decide : ¬ (3 < 2)) bad

theorem bridge : Bridge := by
  intro σ P R F candidate ability uptake calibration g can exclusive
  obtain ⟨a, pure⟩ := ability g can
  exact (calibration g (exclusive g can)).mpr
    (uptake g a ((characterization F (candidate g) a).mpr pure))

end TruthCore.Results.Logic.RevelationPositive
