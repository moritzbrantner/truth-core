import TruthCore.Comparison.Metaethics
namespace TruthCore.Results.Comparison.Metaethics.StevensonEmotivismConsistent
open TruthCore.Comparison.Metaethics

/-- Two people and one moral sentence: one accepts it, the other rejects it,
their attitudes clash; free-standing it expresses the one attitude, and it has a
descriptive meaning. -/
def model : Sig where
  Agent := Bool
  Sentence := Unit
  Ctx := Unit
  Attitude := Unit
  Being := Unit
  Perfection := Unit
  Act := Unit
  Moral := fun _ => True
  TruthApt := fun _ => False
  Holds := fun _ => False
  ObjectiveTruth := fun _ => False
  SaysSomethingBad := fun _ => True
  HasDescriptiveMeaning := fun _ => True
  Accepts := fun x _ => x = true
  Rejects := fun x _ => x = false
  ClashInAttitude := fun _ _ _ => True
  Expresses := fun _ _ _ => True
  free := ()
  Has := fun _ _ => False
  Due := fun _ _ => False
  GoodIn := fun _ _ => False
  Evil := fun _ => False
  GoodAct := fun _ => False
  EvilAct := fun _ => False
  ToBePursued := fun _ => False
  ToBeAvoided := fun _ => False
  p := ()
  germans := true
  robberyNotUnjust := ()

theorem stevensonEmotivismConsistent : StevensonEmotivismConsistent :=
  ⟨model, ⟨fun _ _ => ⟨(), trivial⟩, fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩, trivial⟩

end TruthCore.Results.Comparison.Metaethics.StevensonEmotivismConsistent
