module
public import TruthCore.Explanation.WholeSeriesChoicePolicies
@[expose] public section
namespace TruthCore.Results.Explanation.WholeSeriesChoicePolicies
open TruthCore.Explanation.WholeSeriesReason TruthCore.Explanation.WholeSeriesChoicePolicies

theorem picks_eligible {O : Type} {P : O → Prop} (l : List O) {x : O}
    (h : Picks P l x) : P x := by
  induction l with
  | nil => exact False.elim h
  | cons a t ih =>
    obtain (⟨ha, rfl⟩ | ⟨_, ht⟩) := h
    · exact ha
    · exact ih ht

theorem picks_unique {O : Type} {P : O → Prop} (l : List O) {x y : O}
    (hx : Picks P l x) (hy : Picks P l y) : x = y := by
  induction l with
  | nil => exact False.elim hx
  | cons a t ih =>
    obtain (⟨ha, rfl⟩ | ⟨hna, hx⟩) := hx
    · obtain (⟨_, rfl⟩ | ⟨hn, _⟩) := hy
      · rfl
      · exact False.elim (hn ha)
    · obtain (⟨ha, _⟩ | ⟨_, hy⟩) := hy
      · exact False.elim (hna ha)
      · exact ih hx hy

theorem picks_exists {O : Type} (P : O → Prop) [DecidablePred P] (l : List O) :
    (∃ x, Picks P l x) ↔ ∃ x, x ∈ l ∧ P x := by
  induction l with
  | nil =>
    constructor
    · rintro ⟨x, hx⟩
      exact False.elim hx
    · rintro ⟨x, hx, _⟩
      exact False.elim (List.not_mem_nil hx)
  | cons a t ih =>
    constructor
    · rintro ⟨x, hx⟩
      obtain (⟨ha, rfl⟩ | ⟨_, ht⟩) := hx
      · exact ⟨x, List.mem_cons_self, ha⟩
      · obtain ⟨y, hy, hp⟩ := ih.mp ⟨x, ht⟩
        exact ⟨y, List.mem_cons_of_mem a hy, hp⟩
    · rintro ⟨x, hx, hp⟩
      by_cases ha : P a
      · exact ⟨a, Or.inl ⟨ha, rfl⟩⟩
      · have ht : x ∈ t := by
          cases hx with
          | head => exact False.elim (ha hp)
          | tail _ h => exact h
        obtain ⟨y, hy⟩ := ih.mpr ⟨x, ht, hp⟩
        exact ⟨y, Or.inr ⟨ha, hy⟩⟩

theorem picks_transport {O : Type} {P Q : O → Prop} (l : List O)
    (he : ∀ o, P o ↔ Q o) {x : O} (h : Picks P l x) : Picks Q l x := by
  induction l with
  | nil => exact False.elim h
  | cons a t ih =>
    obtain (⟨ha, hx⟩ | ⟨hn, ht⟩) := h
    · exact Or.inl ⟨(he a).mp ha, hx⟩
    · exact Or.inr ⟨fun hq => hn ((he a).mpr hq), ih ht⟩

/-- Exact formal scopes and the full-fact tied-order control; no historical or
metaphysical adequacy premise is established. -/
theorem certificates : Certificates := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro O P l x y hx hy
    exact picks_unique l hx hy
  · intro O P inst l
    exact picks_exists P l
  · intro W B F O S l h w b r o hc
    exact picks_eligible l (h w b r o hc)
  · intro O P Q l x y he hx hy
    exact picks_unique l (picks_transport l he hx) hy
  · refine ⟨{ exercise with selected := ?_ }⟩
    exact Or.inl ⟨⟨trivial, fun _ _ h => h⟩, rfl⟩
  · intro w b r o _
    exact ⟨trivial, fun _ _ h => h⟩
  · intro h
    have hp := h true () (fun _ => True) true rfl
    rcases hp with ⟨_, he⟩ | ⟨hn, _⟩
    · cases he
    · exact hn ⟨trivial, fun _ _ h => h⟩
  · intro hp
    rcases hp with ⟨_, he⟩ | ⟨hn, _⟩
    · cases he
    · exact hn ⟨trivial, fun _ _ h => h⟩
  · exact id
  · intro W B F O A carries S agenda a h
    obtain ⟨e⟩ := h
    exact ⟨e.toReasonGuidedWholeExercise⟩
  · intro O P l hn hx
    obtain ⟨x, hp⟩ := hx
    exact hn x (picks_eligible l hp)
  · constructor
    · refine ⟨{ selectiveExercise with selected := ?_ }⟩
      exact Or.inl ⟨⟨trivial, fun _ _ h => h⟩, rfl⟩
    · rintro w b r o ⟨rfl, rfl⟩
      exact Or.inl ⟨⟨trivial, fun _ _ h => h⟩, rfl⟩
end TruthCore.Results.Explanation.WholeSeriesChoicePolicies

namespace TruthCore.Results.Explanation.WholeSeriesChoicePolicies
open TruthCore.Explanation.PSRStrength TruthCore.Explanation.WholeSeriesReason
open TruthCore.Explanation.WholeSeriesChoicePolicies
/-- Forget only the procedural agenda condition; all original exercise data,
including the same actual necessary bearer and complete fact valuation, survive. -/
theorem forgetSelection {W B F O : Type} (A : Arena W B F)
    (carries : W → B → F → Prop) (S : Selection W B F O) (agenda : List O) (a : W)
    (h : HasSelectedWholeExercise A carries S agenda a) :
    HasReasonGuidedWholeExercise A carries S a := by
  obtain ⟨e⟩ := h
  exact ⟨e.toReasonGuidedWholeExercise⟩
end TruthCore.Results.Explanation.WholeSeriesChoicePolicies
