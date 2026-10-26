import TruthCore.Comparison.ProblemOfEvil
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question48.Article5

namespace TruthCore.Comparison.ProblemOfEvilCulpa
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Scoped extension for the voluntary-operation question. Separate from the
older general-evil Sig because that signature has no operations or voluntary
control; existing Catholic consistency results make no commitment about culpa.
Operations here are the agent's due operational perfections, so Performs
instantiates Has in the existing privation reading. -/
structure Sig where
  Agent : Type
  Operation : Type
  Voluntary : Agent → Operation → Prop
  Due : Agent → Operation → Prop
  Performs : Agent → Operation → Prop
  Ordered : Agent → Operation → Prop
  Culpa : Agent → Operation → Prop
  Evil : Agent → Prop

/-- Catholic Q-MORAL-GROUNDING cell for culpa, retaining the general privation
account and adding the voluntary-operation classification (q.48 aa.3,5).
No existence premise, semantic bridge to emotivist sentences, or complete
Catholic consistency claim is included. -/
def CatholicOperationalGrounding (s : Sig) : Prop :=
  EvilIsPrivationReading s.Evil s.Due s.Performs ∧
    VoluntaryOperationDefectIsCulpaReading s.Voluntary s.Due s.Performs s.Ordered s.Culpa

end TruthCore.Comparison.ProblemOfEvilCulpa
