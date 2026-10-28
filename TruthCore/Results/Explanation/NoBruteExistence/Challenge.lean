import TruthCore.Explanation.NoBruteExistence
namespace TruthCore.Results.Explanation.NoBruteExistence
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.NoBruteExistence

theorem exclusion {World Being : Type} (m : Model World Being) (w : World) :
    ¬ (NoBruteExistenceAt m w ∧ BruteExistenceAt m w) := by
  sorry

theorem coverage {World Being : Type} (m : Model World Being) (w : World)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    NoBruteExistenceAt m w ∨ BruteExistenceAt m w := by
  sorry

theorem allWorld_iff {World Being : Type} (m : Model World Being) :
    ExistencePSR m ↔ ∀ w, NoBruteExistenceAt m w := by
  sorry

theorem checks {World Being : Type} (m : Model World Being) (w : World)
    (hEM : TruthCore.Logic.ExcludedMiddle) : LocalExistenceBoundary m w := by
  sorry

theorem scopeControl : LocalDoesNotImplyGlobal := by
  sorry
end TruthCore.Results.Explanation.NoBruteExistence
