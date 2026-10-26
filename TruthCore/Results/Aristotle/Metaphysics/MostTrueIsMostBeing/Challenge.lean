import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

namespace TruthCore.Results.Aristotle.Metaphysics.MostTrueIsMostBeing

universe u v

open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The quarta via's step *quae sunt maxime vera, sunt maxime entia, ut dicitur II
Metaphys.* derived from the sentence Aquinas cites, Aristotle, *Metaphysics* II.1,
993b30-31, read in the quarta via's vocabulary: if a thing's standing in truth is its
standing in being (same predicate, same comparison), then whatever is maximal in truth
is maximal in being. Both halves of the correspondence are used: without the first a
maximum in truth need not have being; without the second something could be more a
being than it without being more true. -/
theorem mostTrueIsMostBeing {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (verum esse : Respect)
    (hAsToBeingSoToTruth : AsToBeingSoToTruthReading InAct MoreIn verum esse) :
    MostTrueIsMostBeingReading InAct MoreIn verum esse := by
  sorry

end TruthCore.Results.Aristotle.Metaphysics.MostTrueIsMostBeing
