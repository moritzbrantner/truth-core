import TruthCore.Comparison.MoralError
namespace TruthCore.Results.Comparison.MoralError.AquinasGermansErred
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Metaethics

/-- The Germans held that robbery is not unjust, a moral sentence that is not
true; moral sentences have a truth value (q.94 a.4); so they erred. -/
theorem aquinasGermansErred {Agent Sentence : Type}
    (Accepts : Agent → Sentence → Prop) (Moral TruthApt Holds : Sentence → Prop)
    (germans : Agent) (robberyNotUnjust : Sentence)
    (hTruthApt : MoralJudgmentsAreTruthAptReading Moral TruthApt)
    (hGermans : GermansHeldRobberyNotUnjustReading Accepts Moral Holds germans robberyNotUnjust) :
    SomeMoralError Accepts Moral TruthApt Holds := by
  obtain ⟨hAccepts, hMoral, hNotTrue⟩ := hGermans
  -- INF-AQUINAS-ROBBERY-JUDGMENT-TRUTH-APT
  have hApt : TruthApt robberyNotUnjust := hTruthApt robberyNotUnjust hMoral
  -- INF-AQUINAS-GERMANS-ERRED
  exact ⟨germans, robberyNotUnjust, hMoral, hAccepts, hApt, hNotTrue⟩

/-- Truth-aptness is needed: if moral sentences have no truth value, the Germans
held a moral sentence that is not true, and no one errs. -/
theorem withoutTruthAptnessNoError :
    ∃ (Accepts : Unit → Unit → Prop) (Moral TruthApt Holds : Unit → Prop),
      ¬ MoralJudgmentsAreTruthAptReading Moral TruthApt ∧
      GermansHeldRobberyNotUnjustReading Accepts Moral Holds () () ∧
      ¬ SomeMoralError Accepts Moral TruthApt Holds :=
  ⟨fun _ _ => True, fun _ => True, fun _ => False, fun _ => False,
    fun h => h () trivial, ⟨trivial, trivial, id⟩,
    fun ⟨_, _, _, _, hApt, _⟩ => hApt⟩

end TruthCore.Results.Comparison.MoralError.AquinasGermansErred
