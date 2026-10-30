import TruthCore.Explanation.LawActuality
namespace TruthCore.Results.Explanation.LawActuality
open TruthCore.Explanation.LawActuality
open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Modern.Hume.Induction
open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive

private theorem initial (n : Nat) (b : Bool) : signal n b 0 = true := by
  simp [signal]
private theorem boundary (n : Nat) (b : Bool) : signal n b (n+1) = b := by
  simp [signal]
private theorem samePrefix (n : Nat) (a b : Bool) :
    ∀ i, i < n+1 → signal n a i = signal n b i := by
  intro i hi
  simp [signal, hi]
private theorem follows (n : Nat) (b : Bool) : Follows (law n b) (signal n b) :=
  ⟨initial n b, fun _ => rfl⟩
private theorem unique (n : Nat) (b : Bool) (f : Trace) (hf : Follows (law n b) f) :
    f = signal n b := by
  funext t
  cases t with
  | zero => exact hf.1.trans (initial n b).symm
  | succ t => exact hf.2 t

private theorem different (n : Nat) (a b : Bool) (hab : b ≠ a) :
    ¬ SameHistory (realized n) b a := by
  intro hs
  have hb := (hs b (n+1)).mp (boundary n b).symm
  exact hab (hb.trans (boundary n a))

 theorem certificate : TruthCore.Explanation.LawActuality.Certificate := by
  intro n
  refine ⟨?_, ⟨fun _ _ => Iff.rfl, ?_⟩, ?_, ?_⟩
  · intro b
    exact ⟨fun _ _ _ _ hb hc => hb.trans hc.symm, follows n b, unique n b⟩
  · intro w t
    exact ⟨signal n w t, rfl, fun _ hy => hy⟩
  · intro estimate uses identifies
    have he := uses (signal n false) (signal n true) (samePrefix n false true)
    rw [identifies false, identifies true] at he
    exact Bool.noConfusion he
  · intro a
    have rival : ∃ b : Bool, b ≠ a := by cases a <;> decide
    obtain ⟨b, hab⟩ := rival
    have same : SameEvidence (readings n) (window n) b a := by
      intro r hr
      change (signal n b r.1 = r.2 ↔ signal n a r.1 = r.2)
      rw [samePrefix n b a r.1 hr]
    have noselect := TruthCore.Results.Explanation.HistorySelection.no_selection
      (realized n) (readings n) (window n) a b trivial (different n a b hab) same
    exact ⟨fun hd => noselect ((TruthCore.Results.Explanation.HistorySelection.characterization
      (realized n) (readings n) (window n) a).mp hd), noselect⟩

 theorem omissions : TruthCore.Explanation.LawActuality.Omissions := by
  refine ⟨?_, TruthCore.Results.Causality.ChainInstantiation.controls⟩
  intro n
  refine ⟨fun b => boundary n b, ?_, ?_, ⟨fun _ _ _ => rfl, rfl⟩,
    (fun _ _ => Iff.rfl), ?_, ?_⟩
  · intro uses
    have he := uses (signal n false) (signal n true) (samePrefix n false true)
    simp only [boundary] at he
    exact Bool.noConfusion he
  · intro a b _ same x t
    have he := same (t, signal n a t) trivial
    have eq : signal n b t = signal n a t := he.mpr rfl
    change (x = signal n b t ↔ x = signal n a t)
    rw [eq]
  · rintro ⟨w, x, t, h⟩
    exact h
  · intro b
    exact ⟨signal n b, follows n b, fun f hf => unique n b f hf⟩
end TruthCore.Results.Explanation.LawActuality
