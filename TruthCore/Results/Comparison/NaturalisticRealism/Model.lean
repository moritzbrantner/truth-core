import TruthCore.Comparison.NaturalisticRealism

namespace TruthCore.Results.Comparison.NaturalisticRealism
open TruthCore.Metaethics.NaturalisticRealism

/-- Equal natural benefit units for the two affected people in this fixture. -/
def benefit (_person action : Bool) : Nat := if action then 1 else 0

def totalBenefit (action : Bool) : Nat := benefit false action + benefit true action

/-- An explicitly finite interpretation: two actions, two sentence contents,
two agents. It is a logical witness, not an empirical psychology or a proof
that Railton's reduction or Boyd's causal cluster exists. The impartial
criterion maximizes an equal-weight two-person benefit total. Both people
receive one unit for the first action and zero for the other. This is one
possible realization of a criterion, not Railton's complete aggregation rule. -/
def model : Sig where
  base := {
    Agent := Bool, Sentence := Bool, Ctx := Unit, Attitude := Unit,
    Being := Bool, Perfection := Unit, Act := Bool,
    Moral := fun _ => True, TruthApt := fun _ => True,
    Holds := fun φ => φ = false, ObjectiveTruth := fun φ => φ = false,
    SaysSomethingBad := fun _ => False, HasDescriptiveMeaning := fun _ => True,
    Accepts := fun _ _ => True, Rejects := fun _ _ => False,
    ClashInAttitude := fun _ _ _ => False, Expresses := fun _ _ _ => False,
    free := (), Has := fun b _ => b = true, Due := fun _ _ => True,
    GoodIn := fun b _ => b = true, Evil := fun b => b = false,
    GoodAct := fun a => a = true, EvilAct := fun a => a = false,
    ToBePursued := fun a => a = true, ToBeAvoided := fun a => a = false,
    p := false, germans := false, robberyNotUnjust := true }
  GoodFor := fun _ a => a = true
  SatisfiesObjectiveInterest := fun _ a => a = true
  Right := fun a => a = true
  ImpartialCriterion := fun a => ∀ b : Bool,
    totalBenefit b ≤ totalBenefit a
  FostersGoods := fun a => a = true
  SustainsMechanisms := fun a => a = true
  Ascribes := fun φ a => a = !φ
  Reason := fun _ _ => False

end TruthCore.Results.Comparison.NaturalisticRealism
