import TruthCore.Causality.CreatureSenses

/-! Typed CREATURE senses: the CREATURE_2 → CREATURE_1 bridge derived from the
Fourth-Way consequence, and the caused-esse-is-received bridge of the unified Dei
Filius route derived through it. Analyst formulations, attribution deferred. No
premise is established. -/

namespace TruthCore.Results.Causality.CreatureSenses

open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus IsMaximumIn)
open TruthCore.Case.Catholicism (MaximalCauseWithNoDistinctEsseCause)
open TruthCore.Causality.Round2PerfectionPrimacy
  (CausedInBeingByAnotherIsCreature CreatureEsseIsReceived)
open TruthCore.Causality.CausalMapsBatch1 (CausedPerfectionIsHad)
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Causality.CreatureSenses

/-- Strength order: the general premise (a caused perfection is had by its
effect, in every respect) gives its esse-restricted weak version. -/
theorem causedEsseIsHadFromCausedPerfection {B R : Type}
    (CausesIn : B → B → R → Prop) (InAct : B → R → Prop) (esse : R)
    (h : CausedPerfectionIsHad CausesIn InAct) :
    CausedEsseIsHad CausesIn InAct esse := by
  sorry

/-- The CREATURE_2 → CREATURE_1 bridge. Let c ≠ x cause x's being. Take the
maximum m of the Fourth-Way consequence: it causes the being of every other being
in act, and no being distinct from it causes its being. So x ≠ m (else c, distinct
from m, would cause m's being); x is in act as to being (the weak premise); so m
causes x's being, and x is CREATURE_1 with m as its universal cause. -/
theorem causedInBeingByAnotherIsCreature1 {B R : Type}
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hRoot : MaximalCauseWithNoDistinctEsseCause InAct MoreIn CausesIn esse)
    (hHad : CausedEsseIsHad CausesIn InAct esse) :
    CausedInBeingByAnotherIsCreature CausesIn (IsCreatureOfUniversalCause InAct CausesIn esse) esse := by
  sorry

/-- The bridge of the unified Dei Filius route, derived through CREATURE_1:
what has its being caused by another is CREATURE_1 (the bridge above), and the
esse of every CREATURE_1 is received in some principle (`CreatureEsseIsReceived`
read at CREATURE_1, the q.7 a.2 reading). -/
theorem causedEsseIsReceivedThroughCreature1 {B R P : Type}
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (EsseReceivedIn : B → P → Prop)
    (hBridge : CausedInBeingByAnotherIsCreature CausesIn
      (IsCreatureOfUniversalCause InAct CausesIn esse) esse)
    (hRecv : CreatureEsseIsReceived (IsCreatureOfUniversalCause InAct CausesIn esse)
      EsseReceivedIn) :
    CausedEsseIsReceived CausesIn esse EsseReceivedIn := by
  sorry

open TruthCore.Causality.CreatureSenses.Control in
/-- The controls: CREATURE_2 does not give CREATURE_1 without the bridge; the
weak premise is needed; the whole new bundle has a model with a caused being. -/
theorem controls : TruthCore.Causality.CreatureSenses.Control.Controls := by
  sorry

end TruthCore.Results.Causality.CreatureSenses
