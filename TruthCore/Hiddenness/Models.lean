import TruthCore.Hiddenness.Vocabulary

namespace TruthCore.Hiddenness

/-- A finite interpretation, not a proposed history. At the early time belief
is absent; at the late time it is present. The booleans independently vary the
three disputed conceptual premises for necessity counterexamples. -/
def finiteModel (god love accessEarly believesEarly : Bool) : Sig where
  World := Unit
  Person := Unit
  Time := Bool
  actual := ()
  God := fun _ => god = true
  PerfectLove := fun _ => love = true
  Capable := fun _ _ _ => True
  Resists := fun _ _ _ => False
  Believes := fun _ _ t => t = true ∨ believesEarly = true
  HasConcept := fun _ _ t => t = true ∨ believesEarly = true
  ReflectiveDoubt := fun _ _ _ => False
  Available := fun _ _ t => t = true ∨ accessEarly = true
  Accepts := fun _ _ _ => False
  GoodReason := fun _ _ t => t = false

/-- The Catholic reply's finite interpretation has a gap at the early time
and explicit access later. Its reason predicate is deliberately interpreted,
not proved to describe any actual human life. -/
def delayedModel : Sig := finiteModel true true false false

/-- Non-theistic model with the same human history of nonbelief and later
belief. False religious beliefs can occur; absence of God does not remove the
psychological and cultural phenomena to be explained. Genuine reciprocal
access, however, is unavailable throughout: a false belief does not supply
a nonexistent other party. -/
def nontheisticModel : Sig :=
  { finiteModel false false false false with Available := fun _ _ _ => False }

end TruthCore.Hiddenness
