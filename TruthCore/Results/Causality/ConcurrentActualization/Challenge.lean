import TruthCore.Causality.ConcurrentActualization

namespace TruthCore.Results.Causality.ConcurrentActualization

open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Modal.TemporalHistory (History)

/-- The weak sustaining reading from concurrent actualization. Let `c`, distinct
from `x`, cause `x`'s being, and let `x` be present at `t`. By the reception
bridge `x`'s esse is received in some principle; by concurrent actualization
something gives `x` being at `t`; by concurrence `c` gives `x` being at `t`. So
`c` gives `x` being at every moment at which `x` is present. -/
theorem sustainingOfConcurrentActualization {W B T P Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (EsseReceivedIn : B → P → Prop)
    (hReceived : CausedEsseIsReceived CausesIn esse EsseReceivedIn)
    (hActualized : ConcurrentlyActualized h G EsseReceivedIn)
    (hConcur : CausesOfBeingConcur G CausesIn esse) :
    CausingAnothersBeingIsSustaining h G CausesIn esse := by
  sorry

/-- Strength order: the strong concurrent actualization (a giver distinct from
the thing) entails the weak one. -/
theorem concurrentlyActualizedOfByAnother {W B T P : Type} (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop)
    (hStrong : ConcurrentlyActualizedByAnother h G EsseReceivedIn) :
    ConcurrentlyActualized h G EsseReceivedIn := by
  sorry

/-- Strength order: the sustaining reading `23e04ae5` entails its restriction to
causes distinct from their effect. -/
theorem anothersSustainingOfSustaining {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hSustaining : CausingBeingIsSustaining h G CausesIn esse) :
    CausingAnothersBeingIsSustaining h G CausesIn esse := by
  sorry

/-- The presence step of the immensity sense bridge from the weak sustaining
reading: the creator conjunct of IMMENSE_2 concerns only other beings, so the
restriction to causes distinct from their effect suffices. -/
theorem immense2PresentToAllOfAnothers {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop)
    (hSustaining : CausingAnothersBeingIsSustaining h G CausesIn esse)
    (hInAct : PresentIsInActAsToBeing h InAct esse)
    (hContact : GiverPresentWhenGiving h G) :
    Immense2PresentToAll h G InAct CausesIn esse Infinite := by
  sorry

/-- The immensity sense bridge IMMENSE_2 → IMMENSE_1 (`8bf775e9`) from the weak
sustaining reading, presence-in-act, contact and the narrowed bridge that carries
the rest (place, containment, measure, the other modes of presence,
immediacy). -/
theorem immenseSenseBridgeOfAnothersSustaining {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop) (D : TruthCore.Causality.DeiFiliusAttributeField.Primitives B)
    (hSustaining : CausingAnothersBeingIsSustaining h G CausesIn esse)
    (hInAct : PresentIsInActAsToBeing h InAct esse)
    (hContact : GiverPresentWhenGiving h G)
    (hNarrow : PresentInfiniteCauseOfAllIsImmense h G InAct CausesIn esse Infinite D) :
    TruthCore.Causality.DeiFiliusImmenseIncomprehensible.InfiniteCauseOfAllIsImmense
      InAct CausesIn esse Infinite D := by
  sorry

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control

/-- Rival-reading, omission, strictness and nonvacuity controls
(`Control.Certificate`). -/
theorem controls : TruthCore.Causality.ConcurrentActualization.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ConcurrentActualization
