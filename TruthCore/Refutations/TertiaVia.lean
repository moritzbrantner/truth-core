import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia

/-!
Conclusion propositions of the eternal-world dilemma for the *tertia via*
(owner decision on #143, 2026-10-24). They live outside `TruthCore.Comparison`
because they are not theories: `bind-check` binds them to their statements by
head constant, without unfolding.
-/

namespace TruthCore.Refutations.TertiaVia

open TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- If beings succeed one another without beginning, the past is infinite: the
rival to collective possibility is a rival only on the eternal-world
hypothesis. Stated as a conditional so that the rival's succession is never an
advertised premise. -/
def SuccessionRequiresInfinitePast {Being : Sort u} {Time : Sort v}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time) : Prop :=
  BeingsSucceedWithoutBeginning IsAt Before → PastIsInfinite Before now

/-- The rival's succession without beginning fails. -/
def SuccessionWithoutBeginningFails {Being : Sort u} {Time : Sort v}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) : Prop :=
  ¬ BeingsSucceedWithoutBeginning IsAt Before

end TruthCore.Refutations.TertiaVia
