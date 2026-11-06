import TruthCore.Alternatives.FideismGrammarCases
namespace TruthCore.Results.Alternatives.FideismGrammarCases
open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.FideismGrammarCases

/-- Both fideist bundles fail of the Catholic practice in the two cells where
the practice fixes its own grammar (#1010; owner decision 2026-11-06).
Case 1, authorities: the case bridge gives the definition bridge, and the two
earlier results apply (Dei Filius can. II.1 and can. I.1). Case 2, ordinary
use: the ordinary-use moves that affirm natural knowability and confess the
one true God are the practice's own standard by the case bridge, hence
correct by internal grammar; the first answers to shared reason, which the
cut-off thesis forbids, and the second makes "God" refer, which the no-being
reconstruction denies. Nothing is claimed for the third cell. -/
theorem fideismFailsInAuthorityAndUseCases {Being : Type} (C : CasedPractice Being)
    (god : C.Name)
    (hCouncilII : CouncilDefinesNaturalKnowabilityReading C.toPractice)
    (hCouncilI : CouncilConfessesGodReading C.toNamingPractice god)
    (hShared : NaturalReasonIsSharedReading C.toPractice)
    (hAuthority : AuthorityCaseBridgeReading C)
    (hUse : UseCaseBridgeReading C)
    (hOrdinaryKnow : OrdinaryUseAffirmsNaturalKnowabilityReading C)
    (hOrdinaryConfess : OrdinaryUseConfessesGodReading C god) :
    FideismFailsInAuthorityAndUseCases C god := by
  sorry

/-- The third cell survives: a practice whose grammar is fixed by neither its
authorities nor its ordinary use satisfies every premise above together with
both fideist bundles. -/
theorem neitherCellSurvives :
    ∃ (C : CasedPractice Unit) (god : C.Name),
      GrammarFixedByNeitherReading C ∧
      CouncilDefinesNaturalKnowabilityReading C.toPractice ∧
      CouncilConfessesGodReading C.toNamingPractice god ∧
      NaturalReasonIsSharedReading C.toPractice ∧ AuthorityCaseBridgeReading C ∧
      UseCaseBridgeReading C ∧ OrdinaryUseAffirmsNaturalKnowabilityReading C ∧
      OrdinaryUseConfessesGodReading C god ∧
      (InternalGrammarReading C.toPractice ∧ CutOffReading C.toPractice) ∧
      (InternalGrammarReading C.toPractice ∧ GrammarFixesReferenceReading C.toNamingPractice god ∧
        GodNamesNoBeingReading C.toNamingPractice god) := by
  sorry

/-- The authority-case bridge is needed: in the authority cell, with every other
premise, both bundles hold when the bridge fails. -/
theorem needsAuthorityCaseBridge :
    ∃ (C : CasedPractice Unit) (god : C.Name),
      C.AuthoritiesFixGrammar ∧ ¬ AuthorityCaseBridgeReading C ∧
      CouncilDefinesNaturalKnowabilityReading C.toPractice ∧
      CouncilConfessesGodReading C.toNamingPractice god ∧
      NaturalReasonIsSharedReading C.toPractice ∧ UseCaseBridgeReading C ∧
      OrdinaryUseAffirmsNaturalKnowabilityReading C ∧ OrdinaryUseConfessesGodReading C god ∧
      (InternalGrammarReading C.toPractice ∧ CutOffReading C.toPractice) := by
  sorry

/-- The use-case bridge is needed: in the use cell, with every other premise,
the cut-off pair holds when the bridge fails. -/
theorem needsUseCaseBridge :
    ∃ (C : CasedPractice Unit) (god : C.Name),
      ¬ C.AuthoritiesFixGrammar ∧ C.UseFixesGrammar ∧ ¬ UseCaseBridgeReading C ∧
      CouncilDefinesNaturalKnowabilityReading C.toPractice ∧
      CouncilConfessesGodReading C.toNamingPractice god ∧
      NaturalReasonIsSharedReading C.toPractice ∧ AuthorityCaseBridgeReading C ∧
      OrdinaryUseAffirmsNaturalKnowabilityReading C ∧ OrdinaryUseConfessesGodReading C god ∧
      (InternalGrammarReading C.toPractice ∧ CutOffReading C.toPractice) := by
  sorry

end TruthCore.Results.Alternatives.FideismGrammarCases
