import TruthCore.Greek.Aristotle.Physics

namespace TruthCore.Greek.Aristotle.Physics

/--
Dialectical premise in Aristotle, *Physics* III.4, 203b4-15: if what is infinite in the
unbounded sense had a principle or beginning, that principle would impose a limit on it.

This is deliberately scoped to the chapter's argument about why predecessors treat the
infinite as without a prior principle. It does not make the infinite a separate substance or
anticipate Aristotle's later positive account of potential infinity.

Source: Aristotle, *Physics* III.4, 203b4-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfinitePrincipleWouldLimitReading
    (InfiniteHasPrinciple : Prop)
    (InfiniteIsLimited : Prop) : Prop :=
  InfiniteHasPrinciple → InfiniteIsLimited

/--
Companion premise in Aristotle, *Physics* III.4, 203b4-15: the infinite, precisely insofar
as it is being considered as unbounded, is not limited.

The proposition is a local dialectical premise, not a claim that Aristotle ultimately accepts
an actually infinite separate entity.

Source: Aristotle, *Physics* III.4, 203b4-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteNotLimitedReading
    (InfiniteIsLimited : Prop) : Prop :=
  ¬ InfiniteIsLimited

/--
Dialectical consequence in Aristotle, *Physics* III.4, 203b4-15: an infinite taken as
unbounded has no prior principle or beginning, since such a principle would limit it.

This records the inferential step Aristotle gives while surveying the motivations for making
the infinite a principle. It does not yet settle his own later ontology of the infinite.

Source: Aristotle, *Physics* III.4, 203b4-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteHasNoPrincipleReading
    (InfiniteHasPrinciple : Prop) : Prop :=
  ¬ InfiniteHasPrinciple

end TruthCore.Greek.Aristotle.Physics
