import TruthCore.Comparison.Metaethics
namespace TruthCore.Results.Comparison.Metaethics.CatholicNaturalLawConsistent
open TruthCore.Comparison.Metaethics

/-- Two beings and one perfection: the first has it and is good in it; the
second lacks it although it is due, so there is evil in it. One moral sentence,
"robbery is not unjust", truth-apt, not true, held by the Germans. Two acts: a
good one, to be pursued, and an evil one, to be avoided. -/
def model : Sig where
  Agent := Unit
  Sentence := Unit
  Ctx := Unit
  Attitude := Unit
  Being := Bool
  Perfection := Unit
  Act := Bool
  Moral := fun _ => True
  TruthApt := fun _ => True
  Holds := fun _ => False
  ObjectiveTruth := fun _ => False
  SaysSomethingBad := fun _ => False
  HasDescriptiveMeaning := fun _ => True
  Accepts := fun _ _ => True
  Rejects := fun _ _ => False
  ClashInAttitude := fun _ _ _ => False
  Expresses := fun _ _ _ => False
  free := ()
  Has := fun x _ => x = true
  Due := fun _ _ => True
  GoodIn := fun x _ => x = true
  Evil := fun x => x = false
  GoodAct := fun a => a = true
  EvilAct := fun a => a = false
  ToBePursued := fun a => a = true
  ToBeAvoided := fun a => a = false
  p := ()
  germans := ()
  robberyNotUnjust := ()

theorem catholicNaturalLawConsistent : CatholicNaturalLawConsistent := by
  refine ⟨model, fun _ _ => Iff.rfl, ?_, fun _ _ => trivial, ⟨trivial, trivial, id⟩,
    fun _ h => h, fun _ h => h⟩
  intro x
  cases x
  · exact ⟨fun _ => ⟨(), trivial, Bool.noConfusion⟩, fun _ => rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun ⟨_, _, hNot⟩ => (hNot rfl).elim⟩

end TruthCore.Results.Comparison.Metaethics.CatholicNaturalLawConsistent
