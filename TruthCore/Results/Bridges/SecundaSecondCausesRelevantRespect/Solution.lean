import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
namespace TruthCore.Results.Bridges.SecundaSecondCausesRelevantRespect
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Bridge (#401): the secunda via's strong per se premise
(`STMT-SECOND-EFFICIENT-CAUSES-CAUSE-ONLY-AS-CAUSED`: a cause that is itself
caused in some respect causes only as caused) entails its relevant-respect
reading (`STMT-SECOND-EFFICIENT-CAUSES-CAUSE-AS-CAUSED-IN-RELEVANT-RESPECT`: a
cause that is caused in a respect relevant to its causing causes as caused). The
relevant-respect reading only adds an antecedent. This is the secunda-via
counterpart of the prima via's `StrongPremisesEntailWeakPremises`. -/
theorem secondCausesCauseAsCausedInRelevantRespect {Being Respect : Type}
    (EfficientlyCausesIn : Being → Being → Respect → Prop)
    (CausesAsCaused : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop)
    (hOnly : SecondEfficientCausesCauseOnlyAsCausedReading EfficientlyCausesIn CausesAsCaused) :
    SecondEfficientCausesCauseAsCausedInRelevantRespectReading
      EfficientlyCausesIn CausesAsCaused RelevantTo := by
  intro c x r r' hDistinct hCauses hCaused _hRelevant
  -- Being caused in the relevant respect r' is being caused in some respect.
  obtain ⟨d, hd⟩ := hCaused
  exact hOnly c x r hDistinct hCauses ⟨d, r', hd⟩
end TruthCore.Results.Bridges.SecundaSecondCausesRelevantRespect
