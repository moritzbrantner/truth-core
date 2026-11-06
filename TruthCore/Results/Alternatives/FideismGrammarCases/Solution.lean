module

public import TruthCore.Alternatives.FideismGrammarCases
public import TruthCore.Results.Alternatives.FideismCatholicPractice.Solution
public import TruthCore.Results.Alternatives.FideismReference.Solution

@[expose] public section

namespace TruthCore.Results.Alternatives.FideismGrammarCases
open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.FideismGrammarCases
open TruthCore.Results.Alternatives

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
  intro hCase
  rcases hCase with hA | hU
  · -- Case 1: authorities fix the grammar; the earlier results apply.
    have hDef := hAuthority hA
    exact ⟨FideismCatholicPractice.fideismFailsAsDescription C.toPractice hCouncilII hDef hShared,
      FideismReference.fideistReferenceBundleFails C.toNamingPractice god hCouncilI hDef⟩
  · -- Case 2: ordinary use fixes the grammar.
    refine ⟨?_, ?_⟩
    · intro ⟨hInternal, hCutOff⟩
      obtain ⟨m, hKnow, hOrd⟩ := hOrdinaryKnow
      exact hCutOff m (hShared m hKnow) (hInternal m (hUse hU m hOrd))
    · intro ⟨hInternal, hGrammar, hNoBeing⟩
      obtain ⟨m, hConf, hOrd⟩ := hOrdinaryConfess
      obtain ⟨b, hRef⟩ := hGrammar m (hInternal m (hUse hU m hOrd)) hConf
      exact hNoBeing b hRef

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
  refine ⟨{ Move := Unit, Correct := fun _ => False, OwnStandard := fun _ => False, Defined := fun _ => True, AffirmsNaturalKnowability := fun _ => True, AnswersToSharedReason := fun _ => True, Name := Unit, RefersTo := fun _ _ => False, ConfessesReferent := fun _ _ => True, AuthoritiesFixGrammar := False, UseFixesGrammar := False, InOrdinaryUse := fun _ => True }, (), ⟨id, id⟩, ⟨(), trivial, trivial⟩, ⟨(), trivial, trivial⟩, fun _ _ => trivial,
    fun hA => hA.elim, fun hU => hU.elim, ⟨(), trivial, trivial⟩, ⟨(), trivial, trivial⟩,
    ⟨fun _ h => h, fun _ _ h => h⟩, ⟨fun _ h => h, fun _ h _ => h.elim, fun _ h => h⟩⟩

/-- The authority-case bridge is needed: in the authority cell, with every other
premise, both bundles hold when the bridge fails. -/
theorem needsAuthorityCaseBridge :
    ∃ (C : CasedPractice Unit) (god : C.Name),
      C.AuthoritiesFixGrammar ∧ ¬ AuthorityCaseBridgeReading C ∧
      CouncilDefinesNaturalKnowabilityReading C.toPractice ∧
      CouncilConfessesGodReading C.toNamingPractice god ∧
      NaturalReasonIsSharedReading C.toPractice ∧ UseCaseBridgeReading C ∧
      OrdinaryUseAffirmsNaturalKnowabilityReading C ∧ OrdinaryUseConfessesGodReading C god ∧
      (InternalGrammarReading C.toPractice ∧ CutOffReading C.toPractice) ∧
      (InternalGrammarReading C.toPractice ∧ GrammarFixesReferenceReading C.toNamingPractice god ∧
        GodNamesNoBeingReading C.toNamingPractice god) := by
  refine ⟨{ Move := Unit, Correct := fun _ => False, OwnStandard := fun _ => False, Defined := fun _ => True, AffirmsNaturalKnowability := fun _ => True, AnswersToSharedReason := fun _ => True, Name := Unit, RefersTo := fun _ _ => False, ConfessesReferent := fun _ _ => True, AuthoritiesFixGrammar := True, UseFixesGrammar := False, InOrdinaryUse := fun _ => True }, (), trivial, ?_, ⟨(), trivial, trivial⟩, ⟨(), trivial, trivial⟩,
    fun _ _ => trivial, fun hU => hU.elim, ⟨(), trivial, trivial⟩, ⟨(), trivial, trivial⟩,
    ⟨fun _ h => h, fun _ _ h => h⟩, ⟨fun _ h => h, fun _ h _ => h.elim, fun _ h => h⟩⟩
  intro hBridge
  exact hBridge trivial () trivial

/-- The use-case bridge is needed: in the use cell, with every other premise,
both bundles hold when the bridge fails. -/
theorem needsUseCaseBridge :
    ∃ (C : CasedPractice Unit) (god : C.Name),
      ¬ C.AuthoritiesFixGrammar ∧ C.UseFixesGrammar ∧ ¬ UseCaseBridgeReading C ∧
      CouncilDefinesNaturalKnowabilityReading C.toPractice ∧
      CouncilConfessesGodReading C.toNamingPractice god ∧
      NaturalReasonIsSharedReading C.toPractice ∧ AuthorityCaseBridgeReading C ∧
      OrdinaryUseAffirmsNaturalKnowabilityReading C ∧ OrdinaryUseConfessesGodReading C god ∧
      (InternalGrammarReading C.toPractice ∧ CutOffReading C.toPractice) ∧
      (InternalGrammarReading C.toPractice ∧ GrammarFixesReferenceReading C.toNamingPractice god ∧
        GodNamesNoBeingReading C.toNamingPractice god) := by
  refine ⟨{ Move := Unit, Correct := fun _ => False, OwnStandard := fun _ => False, Defined := fun _ => True, AffirmsNaturalKnowability := fun _ => True, AnswersToSharedReason := fun _ => True, Name := Unit, RefersTo := fun _ _ => False, ConfessesReferent := fun _ _ => True, AuthoritiesFixGrammar := False, UseFixesGrammar := True, InOrdinaryUse := fun _ => True }, (), id, trivial, ?_, ⟨(), trivial, trivial⟩, ⟨(), trivial, trivial⟩,
    fun _ _ => trivial, fun hA => hA.elim, ⟨(), trivial, trivial⟩, ⟨(), trivial, trivial⟩,
    ⟨fun _ h => h, fun _ _ h => h⟩, ⟨fun _ h => h, fun _ h _ => h.elim, fun _ h => h⟩⟩
  intro hBridge
  exact hBridge trivial () trivial

end TruthCore.Results.Alternatives.FideismGrammarCases
