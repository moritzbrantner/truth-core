import TruthCore.Logic.CogitoConcrete
namespace TruthCore.Results.Logic.CogitoConcrete
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Alternatives.ActPotencyRegress (OpiningIsBeingMovedReading)
open TruthCore.Latin.Aquinas.SummaTheologiae (SomethingIsMovedReading)

/-- Concrete fork: an occurring thought, the bearer principle, and the two
open bridges C and E give a concrete being existing at `w₀`. Instantiation of
the bridges at the bearer that `thinkingSubjectOfThought` supplies. -/
theorem inhabitedOfThought {W E Episode : Type}
    (m : Ontic W E) (concrete : E → Prop) (Occurs : Episode → Prop)
    (Bears : E → Episode → Prop) (w₀ : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears concrete)
    (hExists : EveryBearerExistsAt m Occurs Bears w₀) :
    InhabitedConcreteAt m concrete w₀ := by
  sorry

/-- Motion fork: an occurring thought, the bearer principle, the opining
bridge OB and the existing opinion-as-motion premise give the prima via's
observation premise, witnessed by the thought's bearer in the respect of its
content. -/
theorem somethingMovedOfThought {E Episode Respect : Type}
    (Occurs : Episode → Prop) (Bears : E → Episode → Prop)
    (Opines : E → Prop → Prop) (content : Episode → Prop)
    (MovedIn : E → Respect → Prop) (asOpinion : Prop → Respect)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hOpining : BorneThoughtIsOpining Occurs Bears Opines content)
    (hMotion : OpiningIsBeingMovedReading MovedIn Opines asOpinion) :
    SomethingIsMovedReading MovedIn := by
  sorry

/-- Nine finite interpretations: each premise of each fork is needed, and the
event route populates the world without a bearer. -/
theorem omissionControls : OmissionControls := by
  sorry

end TruthCore.Results.Logic.CogitoConcrete
