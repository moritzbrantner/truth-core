import TruthCore.Greek.Aristotle.Physics.BookI.Chapter4

namespace TruthCore.Results.Aristotle.Physics.InfinitePrinciplesUnknowable

open TruthCore.Greek.Aristotle.Physics

/--
If scientific knowledge of a composite requires knowledge of its principles, while those
principles are unknowable, the composite is not scientifically knowable in that sense.
-/
theorem compositeNotKnowableFromInfinitePrinciples
    (CompositeKnowable : Prop)
    (PrinciplesKnowable : Prop)
    (hPrinciplesUnknown : InfinitePrinciplesUnknowableReading PrinciplesKnowable)
    (hRequires :
      CompositeKnowledgeRequiresPrincipleKnowledgeReading
        CompositeKnowable PrinciplesKnowable) :
    CompositeFromInfinitePrinciplesNotKnowableReading CompositeKnowable := by
  sorry

end TruthCore.Results.Aristotle.Physics.InfinitePrinciplesUnknowable
