import TruthCore.Comparison.ProblemOfEvil

/-!
Conclusion propositions of the problem-of-evil refutation (#150). They live
outside `TruthCore.Comparison` because they are not theories: `bind-check`
binds them to their statements by head constant, without unfolding.
-/

namespace TruthCore.Refutations.ProblemOfEvil

open TruthCore.Comparison.ProblemOfEvil
open TruthCore.Latin.Aquinas.SummaTheologiae

universe u

/-- The man-made-evil premise is not true. Asserted as true, as the external
form of the problem of evil needs, it then yields `False`. -/
def MoralEvilPremiseNotTrue {Sentence : Sort u} (Holds : Sentence → Prop)
    (moralEvilPremise : Sentence) : Prop :=
  ¬ Holds moralEvilPremise

/-- The first objection's conditional (if God exists, there is no evil) fails
at `s`. -/
def ObjectionOneFails (s : Sig) : Prop :=
  ¬ GodWouldExcludeAllEvilObjectionReading s.God s.Evil

end TruthCore.Refutations.ProblemOfEvil
