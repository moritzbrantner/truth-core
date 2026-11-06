module

public import TruthCore.Metaethics.ExplanationRivalBoundary

@[expose] public section
namespace TruthCore.Results.Metaethics.ExplanationRivalBoundary.Controls
open TruthCore.Metaethics.ExplanationRivalBoundary
open TruthCore.English.VanRoojen
open TruthCore.Refutations.QuasiRealism
theorem controls : Controls := by
  constructor
  · refine ⟨(fun _ => True), (fun _ => True), (fun _ => True), True.intro,
      (fun _ _ => True.intro), (fun _ _ => True.intro), ?_⟩
    intro h
    exact h () True.intro True.intro True.intro
  · constructor
    · refine ⟨(fun _ => False), (fun _ => True), (fun _ => True),
        (fun _ h => h), ?_, ?_, ?_⟩
      · intro s hs ht hr
        exact hs
      · intro s hs
        exact False.elim hs
      · intro s hs
        exact False.elim hs
    · refine ⟨(fun _ => True), (fun _ => False), (fun _ => False), True.intro,
        ?_, ?_, ?_⟩
      · intro s hs ht hr
        exact ht
      · intro h
        exact h () True.intro
      · intro h
        exact h () True.intro
end TruthCore.Results.Metaethics.ExplanationRivalBoundary.Controls
