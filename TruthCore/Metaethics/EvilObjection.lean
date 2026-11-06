module

public import TruthCore.English.OConnor.Metaethics
public import TruthCore.English.OConnor.ProblemOfEvil
public import TruthCore.English.Rowe.EvidentialEvil
public import TruthCore.Logic.ExcludedMiddle

/-!
# Evil utterances and the force of an objection

Analyst propositions compare a critic's own moral-premise truth condition, an affective
protest, and a hypothetical challenge to a target's permission principle.
These can overlap. An explicit remainder preserves other uses. The named
three-mode coverage proposition is a separate assumption; it is not proved
by failure to find another account, nor identified with all worldviews.

The strict truthless policy reuses O'Connor's four existing readings. The
positive affective analysis does not by itself deny truth-aptness. The target
frame is Rowe's existing being/event/outcome vocabulary: its permission rule
and actual absence of blocking costs are separate open commitments. Suffering
is not identified with moral fault, privation, or an attitude.
-/

@[expose] public section

namespace TruthCore.Metaethics.EvilObjection

open TruthCore.English.OConnor
open TruthCore.English.Rowe

/-- An interpreted critic's utterances. Sentence roles do not fix their
truth values or moral classification; the propositions below constrain them. -/
structure Critic where
  Sentence : Type
  SaysBad : Sentence → Prop
  Moral : Sentence → Prop
  TruthApt : Sentence → Prop
  Holds : Sentence → Prop
  ExpressesDisapproval : Sentence → Prop
  evilUtterance : Sentence
  sufferingReport : Sentence
  internalReport : Sentence

/-- The four premises used by the existing external-emotivism result. -/
def StrictTruthlessPolicy (c : Critic) : Prop :=
  MoralStatementsLackTruthValueReading c.Moral c.TruthApt ∧
    LackingTruthValueExcludesTruthReading c.TruthApt c.Holds ∧
    BadnessAscriptionsAreMoralReading c.SaysBad c.Moral ∧
    ManMadeEvilPremiseSaysSomethingBadReading c.SaysBad c.evilUtterance

/-- Analyst affective analysis over this utterance domain. It leaves open
whether expressions of disapproval are also truth-apt or true. -/
def BadnessAsDisapproval (c : Critic) : Prop :=
  ∀ φ, c.SaysBad φ ↔ c.ExpressesDisapproval φ

/-- The selected evil sentence holds under the critic's own interpretation.
This truth condition is not a speech-act or acceptance predicate, nor an
entire problem-of-evil argument. -/
def OwnTruePremise (c : Critic) : Prop := c.Holds c.evilUtterance

/-- The selected utterance expresses disapproval. This does not alone assert
objective evil or conclude that a deity does not exist. -/
def AffectiveProtest (c : Critic) : Prop := c.ExpressesDisapproval c.evilUtterance

/-- The target's narrow-theism attributes would conflict with its permission
principle in the supplied Rowe frame. The critic's own moral truth predicate
does not occur here. If theism is false this conditional can hold vacuously;
the survivor certificate below explicitly includes a theistic witness. -/
def InternalPermissionChallenge (s : Sig) : Prop :=
  TheisticBeingExists s → ¬ PermissionConstraintReading s

/-- A precise remainder within this diagnostic profile: none of the three
named conditions holds. No claim is made that every other worldview is here. -/
def RemainingUse (c : Critic) (s : Sig) : Prop :=
  ¬ OwnTruePremise c ∧ ¬ InternalPermissionChallenge s ∧ ¬ AffectiveProtest c

/-- Open coverage proposition for this critic/target profile. This is stronger
than coverage with RemainingUse and must be supplied or independently proved.
It does not assert exclusivity or exhaustiveness of philosophical schools. -/
def NamedUseCoverage (c : Critic) (s : Sig) : Prop :=
  OwnTruePremise c ∨ InternalPermissionChallenge s ∨ AffectiveProtest c

/-- Diagnostic coverage with an explicit remainder. -/
def UseCoverageWithRemainder (c : Critic) (s : Sig) : Prop :=
  OwnTruePremise c ∨ InternalPermissionChallenge s ∨ AffectiveProtest c ∨ RemainingUse c s

/-- Under strict truthless semantics the own-true-premise branch is excluded;
the remainder remains available. -/
def EmotivistUseFork (c : Critic) (s : Sig) : Prop :=
  ¬ OwnTruePremise c ∧
    (InternalPermissionChallenge s ∨ AffectiveProtest c ∨ RemainingUse c s)

/-- Conditional elimination only: excluding the own-true branch forces one of
the two named alternatives only when NamedUseCoverage is supplied. -/
def NamedEmotivistAlternatives (c : Critic) (s : Sig) : Prop :=
  ¬ OwnTruePremise c ∧ (InternalPermissionChallenge s ∨ AffectiveProtest c)

/-- A non-moral descriptive report is true exactly when intense suffering
actually occurs. This is not the assertion that the suffering is morally evil. -/
def DescriptiveReport (c : Critic) (s : Sig) : Prop :=
  ¬ c.Moral c.sufferingReport ∧
    (c.Holds c.sufferingReport ↔ ∃ e, s.Occurs e ∧ s.IntenseSuffering e)

/-- A true non-moral report of the target-internal conditional. Its
classification is explicit, not inferred merely from calling it internal. -/
def TrueInternalReport (c : Critic) (s : Sig) : Prop :=
  ¬ c.Moral c.internalReport ∧ c.Holds c.internalReport ∧
    (c.Holds c.internalReport ↔ InternalPermissionChallenge s)

/-- Change only the counterfactual cost relation. All event occurrences,
attributes, powers and evaluative outcome classifications remain the same. -/
def WithoutBlockingCosts (s : Sig) : Sig := { s with Cost := fun _ _ _ => False }

/-- Model controls with certified scope. One critic's truthless moral
semantics and true descriptive report coexist with a permission-satisfying
narrow-theist frame and its cost-free variant. Only the cost relation changes;
the variant has actual gratuitous suffering and a nonvacuous internal challenge.
Affective analysis also has a truth-apt true-evil witness. Finally, the explicit
remainder has a witness where named coverage fails. These are interpretations,
not claims about actual deities, suffering or speakers. -/
def BoundaryModels : Prop :=
  (∃ c : Critic, ∃ s : Sig,
    StrictTruthlessPolicy c ∧ BadnessAsDisapproval c ∧
    DescriptiveReport c s ∧ DescriptiveReport c (WithoutBlockingCosts s) ∧
    TrueInternalReport c (WithoutBlockingCosts s) ∧
    TheisticBeingExists s ∧ PermissionConstraintReading s ∧
    TheisticBeingExists (WithoutBlockingCosts s) ∧
    GratuitousSufferingReading (WithoutBlockingCosts s) ∧
    InternalPermissionChallenge (WithoutBlockingCosts s)) ∧
  (∃ c : Critic, BadnessAsDisapproval c ∧
    c.TruthApt c.evilUtterance ∧ OwnTruePremise c) ∧
  (∃ c : Critic, ∃ s : Sig,
    StrictTruthlessPolicy c ∧ DescriptiveReport c s ∧
    TheisticBeingExists s ∧ PermissionConstraintReading s ∧
    RemainingUse c s ∧ ¬ NamedUseCoverage c s)

end TruthCore.Metaethics.EvilObjection
