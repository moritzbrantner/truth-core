module

public import TruthCore.Comparison.Fideism

@[expose] public section

namespace TruthCore.Results.Alternatives.FideismCatholicPractice
open TruthCore.Alternatives.Fideism

/-- Defeat by consequence of Wittgensteinian fideism (WF-N) as a description of
the Catholic practice (#1010). If the practice's council defines a move that
affirms God's knowability from created things by the natural light of reason
(*Dei Filius* ch. 2, can. II.1), if what the council defines is endorsed by the
practice's own standards, and if that natural reason is reason shared with
those outside the practice, then the fideist pair fails: by its internal-grammar
thesis the defined move is correct, and by its cut-off thesis it is not.
None of the three premises is a fideist commitment, and none is established. -/
theorem fideismFailsAsDescription (P : Practice)
    (hCouncil : CouncilDefinesNaturalKnowabilityReading P)
    (hDefinition : DefinitionIsOwnStandardReading P)
    (hShared : NaturalReasonIsSharedReading P) :
    FideismFailsAsDescription P := by
  intro ⟨hInternal, hCutOff⟩
  obtain ⟨m, hKnow, hDefined⟩ := hCouncil
  -- Internal grammar: the defined move is endorsed by the practice, so correct.
  have hCorrect : P.Correct m := hInternal m (hDefinition m hDefined)
  -- Cut off: a move answering to shared reason is not correct.
  exact hCutOff m (hShared m hKnow) hCorrect

/-- The council premise is needed: a practice whose only move is endorsed by
its own standards, answers to nothing shared, and is not a defined
natural-knowability move satisfies the fideist pair and both bridges. -/
theorem needsCouncil :
    ¬ ∀ P : Practice, DefinitionIsOwnStandardReading P → NaturalReasonIsSharedReading P →
      FideismFailsAsDescription P := by
  intro h
  refine h ⟨Unit, fun _ => True, fun _ => True, fun _ => False, fun _ => False,
    fun _ => False⟩ (fun _ hDefined => hDefined.elim) (fun _ hKnow => hKnow.elim) ?_
  exact ⟨fun _ _ => trivial, fun _ hShared => hShared.elim⟩

/-- The definition bridge is needed (the escape of a fideist who treats
conciliar teaching as theology about the practice, not part of its grammar):
the defined natural-knowability move answers to shared reason, is not endorsed
by the practice's own standards, and is not correct. -/
theorem needsDefinitionIsOwnStandard :
    ¬ ∀ P : Practice, CouncilDefinesNaturalKnowabilityReading P →
      NaturalReasonIsSharedReading P → FideismFailsAsDescription P := by
  intro h
  refine h ⟨Unit, fun _ => False, fun _ => False, fun _ => True, fun _ => True,
    fun _ => True⟩ ⟨(), trivial, trivial⟩ (fun _ _ => trivial) ?_
  exact ⟨fun _ hOwn => hOwn.elim, fun _ _ hCorrect => hCorrect.elim⟩

/-- The shared-reason reading is needed (the practice-internal re-reading of
"naturali humanae rationis lumine", `DISAMB-NATURAL-REASON`): the defined move
is endorsed and correct but answers to nothing shared, so the fideist pair
holds. -/
theorem needsNaturalReasonIsShared :
    ¬ ∀ P : Practice, CouncilDefinesNaturalKnowabilityReading P →
      DefinitionIsOwnStandardReading P → FideismFailsAsDescription P := by
  intro h
  refine h ⟨Unit, fun _ => True, fun _ => True, fun _ => True, fun _ => True,
    fun _ => False⟩ ⟨(), trivial, trivial⟩ (fun _ _ => trivial) ?_
  exact ⟨fun _ _ => trivial, fun _ hShared => hShared.elim⟩

end TruthCore.Results.Alternatives.FideismCatholicPractice
