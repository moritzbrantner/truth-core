import TruthCore.Logic.CogitoSubjectIndependence
namespace TruthCore.Results.Logic.CogitoSubjectIndependence
open TruthCore.Logic.CogitoSubjectIndependence

theorem subjectInference : SubjectInference := by
  intro E S Occurs Bears hThought hBearer
  obtain ⟨e, he⟩ := hThought
  obtain ⟨s, hs⟩ := hBearer e he
  exact ⟨s, e, he, hs⟩

theorem subjectlessEpisodeModel : SubjectlessEpisodeModel := by
  refine ⟨fun _ => True, fun _ _ => False, ⟨(), trivial⟩, ?_⟩
  intro ⟨_, _, _, hs⟩
  exact hs

theorem firstPersonWithoutBearerModel : FirstPersonWithoutBearerModel := by
  refine ⟨fun _ => True, fun _ => True, fun _ _ => False,
    ⟨(), trivial⟩, trivial, ?_⟩
  intro ⟨_, _, _, hs⟩
  exact hs

theorem multipleBearersModel : MultipleBearersModel := by
  refine ⟨fun _ => True, fun _ _ => True, ⟨(), trivial⟩, ?_, trivial, trivial⟩
  intro _ _
  exact ⟨true, trivial⟩

end TruthCore.Results.Logic.CogitoSubjectIndependence
