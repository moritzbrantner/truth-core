import TruthCore.Comparison.Metaethics
namespace TruthCore.Results.Comparison.Metaethics.OConnorEmotivismConsistent
open TruthCore.Comparison.Metaethics

/-- One moral sentence, which says something bad, has no truth value, is not
true and is no objective truth. Everything else is trivial. -/
def model : Sig where
  Agent := Unit
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
  HasDescriptiveMeaning := fun _ => False
  Accepts := fun _ _ => False
  Rejects := fun _ _ => False
  ClashInAttitude := fun _ _ _ => False
  Expresses := fun _ _ _ => False
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
  germans := ()
  robberyNotUnjust := ()

theorem oconnorEmotivismConsistent : OConnorEmotivismConsistent :=
  ⟨model, ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ => trivial⟩, trivial⟩

end TruthCore.Results.Comparison.Metaethics.OConnorEmotivismConsistent
