import TruthCore.Case.Catholicism.StageOne
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Case.Catholicism.FirstUnmovedMoverExistsOrNotFromEm
open TruthCore.Case.Catholicism
open TruthCore.Logic
/-- The #159 gap statement `FirstUnmovedMoverExistsOrNot` is an instance of the
general principle `ExcludedMiddle` (#167). A transcription in the sense of
invariant 16: the proof only instantiates the premise, so this result certifies
that the gap statement *is* an instance of excluded middle, nothing more. -/
theorem firstUnmovedMoverExistsOrNotFromExcludedMiddle {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (hExcludedMiddle : ExcludedMiddle) :
    FirstUnmovedMoverExistsOrNot MovedIn MovesIn := by
  -- Instantiation of the general principle at this proposition.
  exact hExcludedMiddle _
end TruthCore.Results.Case.Catholicism.FirstUnmovedMoverExistsOrNotFromEm
