module

public import TruthCore.Logic.Verificationism
public import TruthCore.Logic.Verificationism.Model

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.Church
open TruthCore.Logic.Verificationism

theorem mem_singleton {α : Type} {a b : α} (h : a ∈ [b]) : a = b := by
  cases h with
  | head => rfl
  | tail _ h => cases h

/-- Church's sentence is directly verifiable: with `o₁` it entails `o₃`, which
`o₁` alone does not entail. -/
theorem churchSentence_direct {L : Language} {F : Frame L} {o₁ o₂ o₃ : L.Sentence}
    (h : ChurchObservations F o₁ o₂ o₃) (s : L.Sentence) :
    DirectlyVerifiable F (churchSentence L o₁ o₂ o₃ s) := by
  obtain ⟨h1, _, h3, h13, _⟩ := h
  refine Or.inr ⟨[o₁], o₃, (by intro h; cases h), ?_, h3, ?_, h13⟩
  · intro x hx; cases mem_singleton hx; exact h1
  · intro w hw
    have hA := hw _ (List.Mem.head _)
    have ho1 := hw o₁ (List.Mem.tail _ (List.Mem.head _))
    rcases (L.holds_disj w _ _).mp hA with hl | hr
    · exact absurd ho1 ((L.holds_neg w o₁).mp ((L.holds_conj w _ _).mp hl).1)
    · exact ((L.holds_conj w _ _).mp hr).1

/-- Church's case split: if his sentence alone entails `o₂`, then `¬s` with `o₃`
entails `o₂`, which `o₃` alone does not, so `¬s` is directly verifiable. -/
theorem neg_direct_of_entails {L : Language} {F : Frame L} {o₁ o₂ o₃ : L.Sentence}
    (h : ChurchObservations F o₁ o₂ o₃) (s : L.Sentence)
    (hA2 : L.Entails [churchSentence L o₁ o₂ o₃ s] o₂) :
    DirectlyVerifiable F (L.neg s) := by
  obtain ⟨_, h2, h3, _, h32⟩ := h
  refine Or.inr ⟨[o₃], o₂, (by intro h; cases h), ?_, h2, ?_, h32⟩
  · intro x hx; cases mem_singleton hx; exact h3
  · intro w hw
    have hns := hw _ (List.Mem.head _)
    have ho3 := hw o₃ (List.Mem.tail _ (List.Mem.head _))
    apply hA2 w
    intro g hg; cases mem_singleton hg
    exact (L.holds_disj w _ _).mpr (Or.inr ((L.holds_conj w _ _).mpr ⟨ho3, hns⟩))

/-- Church's trivialization of Ayer's 1946 criterion: given observation statements o₁, o₂, o₃ with o₁ ⊭ o₃ and o₃ ⊭ o₂, every sentence whose negation is not directly verifiable is indirectly verifiable, through Church's sentence (¬o₁ ∧ o₂) ∨ (o₃ ∧ ¬s). -/
theorem churchTrivialization : ChurchTrivialization := by
  intro L F o₁ o₂ o₃ h s hnd
  have hdir := churchSentence_direct h s
  refine IndirectlyVerifiable.intro [churchSentence L o₁ o₂ o₃ s] o₂ (by intro h; cases h)
    (Or.inl h.2.1) ?_ ?_ ?_
  · intro w hw
    have hs := hw s (List.Mem.head _)
    have hA := hw _ (List.Mem.tail _ (List.Mem.head _))
    rcases (L.holds_disj w _ _).mp hA with hl | hr
    · exact ((L.holds_conj w _ _).mp hl).2
    · exact absurd hs ((L.holds_neg w s).mp ((L.holds_conj w _ _).mp hr).2)
  · intro hA2; exact hnd (neg_direct_of_entails h s hA2)
  · intro p hp; cases mem_singleton hp; exact AdmissiblePremise.direct hdir
/-- The hypotheses are satisfiable: `r 0`, `r 1`, `r 2` of the raven language
are observation statements as Church's construction uses them. -/
theorem churchObservationsInhabited :
    ∃ (L : Language) (F : Frame L) (o₁ o₂ o₃ : L.Sentence), ChurchObservations F o₁ o₂ o₃ := by
  refine ⟨Model.lawLanguage, Model.lawFrame, .r 0, .r 1, .r 2, trivial, trivial, trivial, ?_, ?_⟩
  · intro h
    have h2 := h (Model.oneAt 0) (fun g hg => by
      cases hg with
      | head => show (Model.oneAt 0 0).1 = true; decide
      | tail _ h => cases h)
    exact absurd h2 (by show ¬ (Model.oneAt 0 2).1 = true; decide)
  · intro h
    have h1 := h (Model.oneAt 2) (fun g hg => by
      cases hg with
      | head => show (Model.oneAt 2 2).1 = true; decide
      | tail _ h => cases h)
    exact absurd h1 (by show ¬ (Model.oneAt 2 1).1 = true; decide)
end TruthCore.Results.Logic.Verificationism.Church
