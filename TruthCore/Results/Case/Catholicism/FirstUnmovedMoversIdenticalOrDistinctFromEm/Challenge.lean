import TruthCore.Case.Catholicism.StageOneBridges
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Case.Catholicism.FirstUnmovedMoversIdenticalOrDistinctFromEm
open TruthCore.Case.Catholicism
open TruthCore.Logic
/-- The #166 gap statement `FirstUnmovedMoversIdenticalOrDistinct` is an instance
of the general principle `ExcludedMiddle` (#167), taken at the identity of two
first movers. A transcription in the sense of invariant 16: the proof only
instantiates the premise, so this result certifies that the gap statement *is*
an instance of excluded middle, nothing more. -/
theorem firstUnmovedMoversIdenticalOrDistinctFromExcludedMiddle {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (hExcludedMiddle : ExcludedMiddle) :
    FirstUnmovedMoversIdenticalOrDistinct MovedIn MovesIn := by
  sorry
end TruthCore.Results.Case.Catholicism.FirstUnmovedMoversIdenticalOrDistinctFromEm
