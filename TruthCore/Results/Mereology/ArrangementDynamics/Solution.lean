import TruthCore.Mereology.ArrangementDynamics
namespace TruthCore.Results.Mereology.ArrangementDynamics
open TruthCore.Mereology.ArrangementDynamics

 theorem realization_iff {S M I : Type} (o : S → M) (f : I → S → S) :
    (∃ g : I → M → M, Realizes o f g) ↔ Preserves o f := by
  constructor
  · rintro ⟨g, h⟩ i s t heq
    exact (h i s).trans ((congrArg (g i) heq).trans (h i t).symm)
  · intro h
    refine ⟨fun i => Function.extend o (o ∘ f i) id, ?_⟩
    intro i s
    exact ((h i).extend_apply id s).symm

 theorem histories {S M I : Type} (o : S → M) (f : I → S → S)
    (g : I → M → M) (h : Realizes o f g) :
    ∀ s word, o (run f s word) = run g (o s) word := by
  intro s word
  induction word generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change o (run f (f i s) rest) = run g (g i (o s)) rest
    rw [ih, h i s]

 theorem fixture_realizes (coupled : Bool) :
    Realizes (observe coupled) primitiveStep (macroStep coupled) := by
  intro i s
  cases i with
  | write a b => rfl
  | swap =>
    cases coupled <;> cases s with
    | mk a b => cases a <;> cases b <;> rfl

 theorem no_flip_reduction : ¬ ∃ g : Bool → Bool, ∀ s,
    observe true (flipLeft s) = g (observe true s) := by
  rintro ⟨g, h⟩
  have h₁ := h (false, false)
  have h₂ := h (false, true)
  change false = g false at h₁
  change true = g false at h₂
  exact Bool.noConfusion (h₁.trans h₂.symm)

 theorem controls : Certificate := by
  refine ⟨fun _ _ _ => realization_iff, fun _ _ _ => histories,
    fixture_realizes, ?_, ?_, ?_, no_flip_reduction⟩
  · rintro ⟨a, b, heq, hne⟩
    exact hne heq
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
end TruthCore.Results.Mereology.ArrangementDynamics
