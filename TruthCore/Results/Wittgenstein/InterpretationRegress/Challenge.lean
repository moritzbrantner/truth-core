import TruthCore.German.Wittgenstein.RuleFollowing
namespace TruthCore.Results.Wittgenstein.InterpretationRegress
open TruthCore.German.Wittgenstein.RuleFollowing

/-- The regress of *Philosophische Untersuchungen* §§198, 201: if an item (an
application of a rule, or an interpretation of it) is determined only through
a determined interpretation of it, and there is no endless chain of
interpretations behind interpretations, then no item is determined. By
well-founded induction on "is an interpretation of". -/
theorem interpretationRegress {Item : Type}
    (Interprets : Item → Item → Prop) (Determined : Item → Prop)
    (hOnlyThrough : DeterminedOnlyThroughInterpretationReading Interprets Determined)
    (hNoEndless : NoEndlessInterpretationReading Interprets) :
    NothingDeterminedReading Determined := by
  sorry

/-- The fork (§201): together with the premise that some application is
determined, the two regress premises are inconsistent. So a reader who keeps
determination (the diagnostic reading) must give up the interpretation premise
or admit an endless regress; a reader who keeps the interpretation premise and
finiteness (Kripke's sceptic) must deny that any application is determined. -/
theorem regressFork {Item : Type}
    (Interprets : Item → Item → Prop) (Determined : Item → Prop) :
    ¬ (DeterminedOnlyThroughInterpretationReading Interprets Determined ∧
        NoEndlessInterpretationReading Interprets ∧
        SomeApplicationDeterminedReading Determined) := by
  sorry

/-- The interpretation premise is needed: with no interpretations at all, the
relation is well-founded and every item is determined (a grasp that is not an
interpretation, §201). -/
theorem needsOnlyThroughInterpretation :
    ¬ ∀ (Item : Type) (Interprets : Item → Item → Prop) (Determined : Item → Prop),
      NoEndlessInterpretationReading Interprets → NothingDeterminedReading Determined := by
  sorry

/-- Finiteness is needed: with an endless chain (each natural number interpreted
by its successor) and every item determined, the interpretation premise holds
and something is determined ("Deutung hinter Deutung", each giving a moment's
rest). -/
theorem needsNoEndless :
    ¬ ∀ (Item : Type) (Interprets : Item → Item → Prop) (Determined : Item → Prop),
      DeterminedOnlyThroughInterpretationReading Interprets Determined →
        NothingDeterminedReading Determined := by
  sorry

end TruthCore.Results.Wittgenstein.InterpretationRegress
