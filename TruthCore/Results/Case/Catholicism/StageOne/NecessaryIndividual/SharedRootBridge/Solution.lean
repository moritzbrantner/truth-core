import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.EmptyWorldFork

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.SharedRootBridge
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- Constructive biconditional: a shared root is necessary only with
successor-relative population of every accessible world. -/
theorem checks : SharedRootBridgeLaw := by
  intro World Individual F present w
  constructor
  · rintro ⟨root, hRoot⟩
    exact ⟨deRe_to_deDicto F present w ⟨root, hRoot⟩,
      ⟨root, fun next hAccess _ => hRoot next hAccess⟩⟩
  · rintro ⟨hPopulated, ⟨root, hShared⟩⟩
    exact ⟨root, fun next hAccess =>
      hShared next hAccess (hPopulated next hAccess)⟩
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.SharedRootBridge
