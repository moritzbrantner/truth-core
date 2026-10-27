import TruthCore.Logic.CogitoConcrete
import TruthCore.Results.Logic.CogitoSubject.Solution
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
  obtain ⟨b, e, he, hb⟩ :=
    TruthCore.Results.Logic.CogitoSubject.thinkingSubjectOfThought Occurs Bears hOccurs hBearer
  exact ⟨b, hConcrete b e he hb, hExists b e he hb⟩

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
  obtain ⟨b, e, he, hb⟩ :=
    TruthCore.Results.Logic.CogitoSubject.thinkingSubjectOfThought Occurs Bears hOccurs hBearer
  exact ⟨b, asOpinion (content e), hMotion b (content e) (hOpining b e he hb)⟩

/-- Nine finite interpretations: each premise of each fork is needed, and the
event route populates the world without a bearer. -/
theorem omissionControls : OmissionControls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- O omitted
  · exact ⟨unitOntic False, fun _ => False, fun _ => False, fun _ _ => False,
      fun ⟨_, h⟩ => h, fun _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim,
      fun ⟨_, h, _⟩ => h⟩
  -- B omitted
  · exact ⟨unitOntic False, fun _ => False, fun _ => True, fun _ _ => False,
      ⟨(), trivial⟩, fun h => (h () trivial).elim fun _ h => h,
      fun _ _ _ h => h.elim, fun _ _ _ h => h.elim, fun ⟨_, h, _⟩ => h⟩
  -- C omitted: the bearer exists but is not concrete
  · exact ⟨unitOntic True, fun _ => False, fun _ => True, fun _ _ => True,
      ⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun h => h () () trivial trivial,
      fun _ _ _ _ => trivial, fun ⟨_, h, _⟩ => h⟩
  -- E omitted: the bearer is concrete but does not exist at the world
  · exact ⟨unitOntic False, fun _ => True, fun _ => True, fun _ _ => True,
      ⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial,
      fun h => h () () trivial trivial, fun ⟨_, _, h⟩ => h⟩
  -- event route without a bearer
  · exact ⟨unitOntic True, fun _ => True, fun _ => True, fun _ _ => False, id,
      ⟨(), trivial⟩, fun _ _ => ⟨trivial, trivial⟩,
      fun h => (h () trivial).elim fun _ h => h, ⟨(), trivial, trivial⟩⟩
  -- motion fork, O omitted
  · exact ⟨fun _ => False, fun _ _ => True, fun _ _ => False, fun _ _ => False,
      fun ⟨_, h⟩ => h, fun _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h,
      fun ⟨_, _, h⟩ => h⟩
  -- motion fork, B omitted
  · exact ⟨fun _ => True, fun _ _ => False, fun _ _ => False, fun _ _ => False,
      ⟨(), trivial⟩, fun h => (h () trivial).elim fun _ h => h,
      fun _ _ _ h => h.elim, fun _ _ h => h, fun ⟨_, _, h⟩ => h⟩
  -- motion fork, OB omitted: the bearer opines nothing
  · exact ⟨fun _ => True, fun _ _ => True, fun _ _ => False, fun _ _ => False,
      ⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun h => h () () trivial trivial,
      fun _ _ h => h, fun ⟨_, _, h⟩ => h⟩
  -- motion fork, opinion-as-motion omitted: the bearer opines and is unmoved
  · exact ⟨fun _ => True, fun _ _ => True, fun _ _ => True, fun _ _ => False,
      ⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial,
      fun h => h () True trivial, fun ⟨_, _, h⟩ => h⟩

end TruthCore.Results.Logic.CogitoConcrete
