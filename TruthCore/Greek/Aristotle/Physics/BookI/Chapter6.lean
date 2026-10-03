import TruthCore.Greek.Aristotle.Physics.BookI.Chapter5

namespace TruthCore.Greek.Aristotle.Physics

/--
Opening enumeration in Aristotle, *Physics* I.6, 189a11-12: the inquiry considers whether
the natural principles number one, two, three, or more than three.

These are alternatives in the inquiry, not claims that any one case has yet been established.

Source: Aristotle, *Physics* I.6, 189a11-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalPrincipleCountCasesReading
    (OnePrinciple TwoPrinciples ThreePrinciples MoreThanThreePrinciples : Prop) : Prop :=
  OnePrinciple ∨ TwoPrinciples ∨ ThreePrinciples ∨ MoreThanThreePrinciples

/--
First exclusion in Aristotle, *Physics* I.6, 189a11-12: the principles cannot number one,
because the contraries established in I.5 are not one.

The declaration records the numerical exclusion without treating every pair of opposed
predicates as natural principles.

Source: Aristotle, *Physics* I.6, 189a11-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalPrincipleCountNotOneReading (OneNaturalPrinciple : Prop) : Prop :=
  ¬ OneNaturalPrinciple

/--
Second exclusion in Aristotle, *Physics* I.6, 189a12-20: the natural principles are not
infinite in number. Aristotle appeals to knowability, the unity of primary contrariety in a
genus, the sufficiency of finitely many principles, and the derivation of later contraries.

This conclusion is narrower than the I.4 claim about principles infinite in both number and
kind and therefore receives its own statement identity.

Source: Aristotle, *Physics* I.6, 189a12-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalPrinciplesNotInfiniteInNumberReading
    (InfinitelyManyNaturalPrinciples : Prop) : Prop :=
  ¬ InfinitelyManyNaturalPrinciples

/--
First reason for a third item in Aristotle, *Physics* I.6, 189a20-27: opposed principles do
not produce one another; both act upon a third subject distinct from them.

The claim does not yet identify that subject with Aristotle's mature account of matter.

Source: Aristotle, *Physics* I.6, 189a20-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContraryPrinciplesActOnThirdSubjectReading
    (ContraryPrinciplesActOnThirdSubject : Prop) : Prop :=
  ContraryPrinciplesActOnThirdSubject

/--
Predication argument in Aristotle, *Physics* I.6, 189a27-32: if the contraries are predicated
of a substratum, that substratum is prior to the predicates and is itself a principle.

The implication preserves the argumentative condition instead of asserting that every
predicate has the same kind of ontological priority relation.

Source: Aristotle, *Physics* I.6, 189a27-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SubstratumPriorToContraryPredicatesReading
    (ContrariesPredicatedOfSubstratum SubstratumPriorToContraryPredicates : Prop) : Prop :=
  ContrariesPredicatedOfSubstratum → SubstratumPriorToContraryPredicates

/--
Substance constraint in Aristotle, *Physics* I.6, 189a32-34: substance is not contrary to
substance. Aristotle uses this against deriving substances from contrary non-substances.

This records the explicit constraint, not the stronger converse or a complete theory of
substance.

Source: Aristotle, *Physics* I.6, 189a32-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SubstanceNotContraryToSubstanceReading (SubstanceContraryToSubstance : Prop) : Prop :=
  ¬ SubstanceContraryToSubstance

/--
Conditional conclusion in Aristotle, *Physics* I.6, 189a34-189b3: retaining both the prior
argument for contrary principles and the new substratum argument requires positing a third
item underlying the contraries.

The conditional leaves the two supporting arguments independently identified and does not
decide whether the underlying item is water, fire, air, or an intermediate nature.

Source: Aristotle, *Physics* I.6, 189a34-189b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ThirdSubstratumRequiredReading
    (ContraryPrinciplesArgument SubstratumArgument ThirdSubstratumRequired : Prop) : Prop :=
  ContraryPrinciplesArgument ∧ SubstratumArgument → ThirdSubstratumRequired

/--
Upper-bound conclusion in Aristotle, *Physics* I.6, 189b16-27: more than three primary
principles are not required. One subject suffices for being acted upon, while an additional
primary contrariety would either require a separate subject or be redundant.

The declaration records Aristotle's conclusion without importing a modern minimality metric.

Source: Aristotle, *Physics* I.6, 189b16-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalPrincipleCountNotMoreThanThreeReading
    (MoreThanThreeNaturalPrinciples : Prop) : Prop :=
  ¬ MoreThanThreeNaturalPrinciples

/--
Closing conclusion of Aristotle, *Physics* I.6, 189b27-29: the natural principles number
either two or three. The chapter explicitly leaves which of these alternatives is correct as
a substantial aporia for the account beginning in I.7.

The formal support from the count cases and the two exclusions is represented separately as
an inference application and mechanically verified argument.

Source: Aristotle, *Physics* I.6, 189b27-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalPrincipleCountTwoOrThreeReading
    (TwoNaturalPrinciples ThreeNaturalPrinciples : Prop) : Prop :=
  TwoNaturalPrinciples ∨ ThreeNaturalPrinciples

end TruthCore.Greek.Aristotle.Physics
