/-! Peter Railton, “Moral Realism” (1986), verified original pp.173–176,
190–191. Only the displayed identification claims are encoded. The idealized
agent is an epistemic device; its desires do not create objective interests.
Full information, interpersonal comparison and the adequacy of the proposed
natural criterion remain substantive, unproved commitments. -/
namespace TruthCore.English.Railton

/-- pp.175–176: non-moral goodness for a person consists in satisfying an
objective interest. `Act` includes outcomes pursued by an action. -/
def WelfareReading {Agent Act : Type}
    (GoodFor SatisfiesObjectiveInterest : Agent → Act → Prop) : Prop :=
  ∀ x a, GoodFor x a ↔ SatisfiesObjectiveInterest x a

/-- pp.190–191: moral rightness is assessed by fully informed instrumental
rationality from an impartial standpoint counting affected interests equally.
The parameter is that criterion, not an individual's current approval. -/
def RightnessReading {Act : Type} (Right ImpartialCriterion : Act → Prop) : Prop :=
  ∀ a, Right a ↔ ImpartialCriterion a

end TruthCore.English.Railton
