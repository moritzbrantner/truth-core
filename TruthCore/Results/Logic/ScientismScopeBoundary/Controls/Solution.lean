module
public import TruthCore.Logic.ScientismScopeBoundary
@[expose] public section
namespace TruthCore.Results.Logic.ScientismScopeBoundary.Controls
open TruthCore.Logic.Scientism
open TruthCore.Logic.ScientismScopeBoundary
theorem controls : Controls := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨(fun _ => True), (fun c => c = true)⟩, (fun c => c = true), ?_, ?_, ?_, ?_⟩
    · intro c hIn _
      exact hIn
    · exact ⟨false, True.intro, fun h => Bool.noConfusion h⟩
    · exact ⟨true, rfl, True.intro, rfl⟩
    · intro h
      exact Bool.noConfusion (h false True.intro (fun h => Bool.noConfusion h))
  · refine ⟨⟨(fun _ => True), (fun c => c = true)⟩, (fun c => c = false), ?_, ?_, ?_⟩
    · intro c _ hNot
      cases c
      · rfl
      · exact False.elim (hNot rfl)
    · intro h
      exact Bool.noConfusion (h true True.intro)
    · exact ⟨false, True.intro, fun h => Bool.noConfusion h⟩
  · refine ⟨⟨(fun _ => True), (fun _ => False)⟩, (fun c => c = true), ?_, ?_, ?_⟩
    · intro _
      exact ⟨true, rfl, True.intro, fun h => h⟩
    · intro h
      exact Bool.noConfusion (h false True.intro (fun h => h))
    · exact ⟨false, True.intro, fun h => h⟩
end TruthCore.Results.Logic.ScientismScopeBoundary.Controls
