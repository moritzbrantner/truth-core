module
public import TruthCore.Causality.SurveySourceEndpointControls
@[expose] public section
namespace TruthCore.Results.Causality.SurveySourceEndpointControls
open TruthCore.Causality.SurveySourceEndpointControls

theorem endpointObstruction : EndpointObstruction := by
  refine ⟨?_, ?_, True.intro, ?_, ?_, ?_, ?_⟩
  · rintro v c ⟨_, z, _, absent⟩
    exact (absent True.intro).elim
  · intro _ _ _ _ _; trivial
  · refine ⟨(), True.intro, ?_⟩
    intro all
    have bad := all ⟨(), True.intro⟩ ⟨(), True.intro⟩
      (Relation.ReflTransGen.refl)
    obtain ⟨y, _, impossible⟩ := bad
    exact impossible
  · exact ⟨(), True.intro, (fun _ _ => True.intro), fun ⟨_, h⟩ => h⟩
  · rintro ⟨_, _, h⟩; exact h
  · rintro ⟨_, impossible, _⟩; exact impossible
end TruthCore.Results.Causality.SurveySourceEndpointControls
