module

public import TruthCore.Alternatives.Fideism
public import TruthCore.Logic.ExcludedMiddle

/-!
# Conciliar theology and a practice's own standards

The existing Defined and OwnStandard fields are retained. A theological-content
role and a role in first-order religious life are separate predicates on the
same moves, not logical quantifier orders or two practices. A doctrinal sentence
can function as confession; the role labels are not made disjoint by definition.
Whether theological formulations are excluded from own-standard endorsement is
therefore a separate explicit proposition, not inferred from calling them
second-order theology. No actual liturgical or institutional fact is asserted. The existing
CasedPractice.InOrdinaryUse records ordinary practitioners' uptake and who
fixes grammar, whereas this profile separates content from a role in religious
life without choosing a grammar fixer or assuming uptake determines norms.
Those predicates are not identified; naming fields are not needed here.

The raw earlier theology-not-grammar reconstruction remains unchanged. This
profile studies a modest descriptive sibling and the stronger exclusion needed
to oppose DefinitionIsOwnStandardReading. Actual Defined witnesses prevent a
vacuous refutation. Mixed defined moves are a precise further profile beyond
two uniform readings; named uniform coverage stays open. This is not a census
of all philosophies of theology, grammar or authority.
-/

@[expose] public section

namespace TruthCore.Alternatives.ConciliarGrammarDefinitions

open TruthCore.Alternatives.Fideism

/-- Content and practical-life roles, independently of normative endorsement. -/
structure RoleProfile (P : Practice) where
  Theological : P.Move → Prop
  InReligiousLife : P.Move → Prop

/-- Descriptive content proposition, not exclusion from the practice's norms. -/
def DefinitionsAreTheological (P : Practice) (R : RoleProfile P) : Prop :=
  ∀ m, P.Defined m → R.Theological m

/-- A modest descriptive reading: definitions are theological formulations;
endorsed moves belong to religious life. The roles can overlap. -/
def DescriptiveTheologyGrammar (P : Practice) (R : RoleProfile P) : Prop :=
  DefinitionsAreTheological P R ∧ (∀ m, P.OwnStandard m → R.InReligiousLife m)

/-- The substantive exclusion needed for the strong opponent reading. -/
def TheologyExcludedFromOwnStandards (P : Practice) (R : RoleProfile P) : Prop :=
  ∀ m, R.Theological m → ¬ P.OwnStandard m

/-- Actual nonempty definition scope; no natural-knowability content is needed
for conflict with the definition-to-own-standard bridge. -/
def DefinedMoveExists (P : Practice) : Prop := ∃ m, P.Defined m

/-- Positive ordinary-life endorsement witness, making the countermodels more
than an absence of every own standard. -/
def ReligiousLifeOwnMoveExists (P : Practice) (R : RoleProfile P) : Prop :=
  ∃ m, R.InReligiousLife m ∧ P.OwnStandard m

/-- Explicit all-nonendorsed profile for defined moves. -/
def DefinitionsNeverOwn (P : Practice) : Prop :=
  ∀ m, P.Defined m → ¬ P.OwnStandard m

/-- Precise further profile with actual endorsed and nonendorsed definitions. -/
def MixedDefinitionStatus (P : Practice) : Prop :=
  (∃ m, P.Defined m ∧ P.OwnStandard m) ∧
  (∃ m, P.Defined m ∧ ¬ P.OwnStandard m)

/-- Open coverage by the two named uniform endorsement profiles. -/
def NamedDefinitionStatusCoverage (P : Practice) : Prop :=
  DefinitionIsOwnStandardReading P ∨ DefinitionsNeverOwn P

/-- Structural coverage of the two universals or actual mixed witnesses. -/
def DefinitionStatusCases (P : Practice) : Prop :=
  DefinitionIsOwnStandardReading P ∨ DefinitionsNeverOwn P ∨ MixedDefinitionStatus P

/-- Exact opposing sibling of the existing definition bridge. -/
def DefinitionBridgeRejected (P : Practice) : Prop :=
  ¬ DefinitionIsOwnStandardReading P

/-- Both universal endorsement profiles fail, not theology or religious life. -/
def UniformDefinitionStatusRejected (P : Practice) : Prop :=
  ¬ DefinitionIsOwnStandardReading P ∧ ¬ DefinitionsNeverOwn P

/-- Four controls with positive ordinary-life endorsement: descriptive theology
coexists with the bridge; explicit exclusion yields an actual bridge failure
and the old fideist pair; mixed status survives; an empty definition domain
permits universal overlap. No real-world interpretation is thereby established. -/
def ConciliarGrammarModels : Prop :=
  (∃ P : Practice, ∃ R : RoleProfile P,
    DescriptiveTheologyGrammar P R ∧ DefinedMoveExists P ∧ ReligiousLifeOwnMoveExists P R ∧
    DefinitionIsOwnStandardReading P ∧ ¬ TheologyExcludedFromOwnStandards P R) ∧
  (∃ P : Practice, ∃ R : RoleProfile P,
    DescriptiveTheologyGrammar P R ∧ DefinedMoveExists P ∧ ReligiousLifeOwnMoveExists P R ∧
    TheologyExcludedFromOwnStandards P R ∧ DefinitionsNeverOwn P ∧ DefinitionBridgeRejected P ∧
    CouncilDefinesNaturalKnowabilityReading P ∧ NaturalReasonIsSharedReading P ∧
    InternalGrammarReading P ∧ CutOffReading P) ∧
  (∃ P : Practice, ∃ R : RoleProfile P,
    DescriptiveTheologyGrammar P R ∧ DefinedMoveExists P ∧ ReligiousLifeOwnMoveExists P R ∧
    MixedDefinitionStatus P ∧ UniformDefinitionStatusRejected P) ∧
  (∃ P : Practice, ∃ R : RoleProfile P,
    ¬ DefinedMoveExists P ∧ ReligiousLifeOwnMoveExists P R ∧
    DefinitionIsOwnStandardReading P ∧ DefinitionsNeverOwn P ∧
    TheologyExcludedFromOwnStandards P R)

end TruthCore.Alternatives.ConciliarGrammarDefinitions
