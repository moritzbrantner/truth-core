import TruthCore.Causality.AtomisticUniversalCausePriority
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.AtomisticUniversalCausePriority
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.AtomisticUniversalCausePriority

theorem causedSimplePart {B : Type} [PartialOrder B] (G : Graph B)
    (hWF : ProperPartWF B) (hP6 : CausedCompositeHasCausedProperPart G)
    (hEM : ExcludedMiddle) : EveryCausedObjectHasCausedSimplePart G := by
  sorry

theorem universalPriority {B : Type} [PartialOrder B] (G : Graph B)
    (Prior : B → B → Prop)
    (hPop : ObjectPopulation B) (hWF : ProperPartWF B)
    (hCover : ConditionalCausedSimpleCover G) (hNoOverlap : CauseEffectNonoverlap G)
    (hActivity : CausalActivity G) (hEM : ExcludedMiddle)
    (hP6 : CausedCompositeHasCausedProperPart G)
    (hCausePrior : CausePriorToEffectParts G Prior)
    (hPartPrior : ProperPartsPrior Prior)
    (hTrans : TransitiveExistentialPriority Prior) : UniversalCausePriority G Prior := by
  sorry

theorem consistency : TruthCore.Causality.AtomisticUniversalCausePriority.Consistency := by
  sorry

end TruthCore.Results.Causality.AtomisticUniversalCausePriority
