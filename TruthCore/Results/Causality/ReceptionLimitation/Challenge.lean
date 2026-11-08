import TruthCore.Causality.ReceptionLimitation

namespace TruthCore.Results.Causality.ReceptionLimitation
open TruthCore.Causality.ReceptionLimitation
open TruthCore.Causality.EsseReceptionDefinitionFork (Frame IdentityScopedOwnEssence)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Latin.Aquinas.DeEnte (ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception
  (UnlimitedEsseIsInfiniteReading)
open TruthCore.Causality.WholePowerPerfection
open TruthCore.Causality.RootPurity (UnlimitedDeterminationsArePure)

/-- A being with no represented limiting principle is its own being: if its esse
were received in some principle, that principle would be its essence (identity
scope), in receptive potency to its esse (De ente c.3), hence to itself, which
irreflexivity excludes; an esse received in nothing is own being (q.7 a.1). -/
theorem unlimitedIsOwnBeing (f : Frame) (Composite : f.Being → Prop)
    (PriorSimply : f.Being → f.Being → Prop) (OwnBeing : f.Being → Prop)
    (ReceptivePotencyTo : f.Principle → f.Principle → Prop)
    (hNature : IdentityScopedOwnEssence f)
    (hPotency : ReceiverInPotencyToReceivedEsseReading f.esseOf
      (f.Received f.selected) ReceptivePotencyTo)
    (hIrreflexive : NothingInReceptivePotencyToItself ReceptivePotencyTo)
    (hUnreceived : UnreceivedEsseIsOwnBeing (f.Received f.selected) OwnBeing) :
    UnlimitedIsOwnBeing Composite PriorSimply f.essenceOf f.esseOf OwnBeing := by
  sorry

/-- A being with no represented limiting principle has only pure determinations:
it is its own being (as above), so no recipient (q.4 a.1 ad 3), so all its
determinations are pure (q.7 a.1 generalized). -/
theorem unlimitedDeterminationsArePure {D : Type} (f : Frame) (Composite : f.Being → Prop)
    (PriorSimply : f.Being → f.Being → Prop) (OwnBeing Recipient : f.Being → Prop)
    (ReceptivePotencyTo : f.Principle → f.Principle → Prop)
    (Has : f.Being → D → Prop) (Pure : D → Prop)
    (hNature : IdentityScopedOwnEssence f)
    (hPotency : ReceiverInPotencyToReceivedEsseReading f.esseOf
      (f.Received f.selected) ReceptivePotencyTo)
    (hIrreflexive : NothingInReceptivePotencyToItself ReceptivePotencyTo)
    (hUnreceived : UnreceivedEsseIsOwnBeing (f.Received f.selected) OwnBeing)
    (hNoRecipient : OwnBeingIsNoRecipient OwnBeing Recipient)
    (hPure : NonRecipientDeterminationsArePure Recipient Has Pure) :
    UnlimitedDeterminationsArePure Composite PriorSimply f.essenceOf f.esseOf Has Pure := by
  sorry

/-- Whatever is infinite has every pure perfection: its esse is not limited
(premise: the infinite is not finite, q.7 a.1 read conversely), so not received (q.7 a.2), so it is its own being
(q.7 a.1), which lacks no perfection of being (SCG I.28), and every pure
perfection is one (q.4 a.2). -/
theorem infiniteHasEveryPurePerfection {B P D : Type}
    (EsseLimited Infinite OwnBeing : B → Prop) (EsseReceivedIn : B → P → Prop)
    (Has : B → D → Prop) (Pure OfBeing : D → Prop)
    (hInfinite : InfiniteEsseIsUnlimited EsseLimited Infinite)
    (hContracted : ReceivedEsseIsLimited EsseLimited EsseReceivedIn)
    (hUnreceived : UnreceivedEsseIsOwnBeing EsseReceivedIn OwnBeing)
    (hWhole : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (hPertain : PurePerfectionsPertainToBeing Pure OfBeing) :
    InfiniteHasEveryPurePerfection Infinite Has Pure := by
  sorry

/-- Second derivation of the q.7 a.1 leaf: an unlimited esse is not received
(q.7 a.2), so its bearer is its own being (q.7 a.1), which is infinite (q.7 a.1
with own being as the primitive). -/
theorem unlimitedEsseIsInfinite {B P : Type}
    (EsseLimited Infinite OwnBeing : B → Prop) (EsseReceivedIn : B → P → Prop)
    (hContracted : ReceivedEsseIsLimited EsseLimited EsseReceivedIn)
    (hUnreceived : UnreceivedEsseIsOwnBeing EsseReceivedIn OwnBeing)
    (hOwnInfinite : OwnBeingIsInfinite OwnBeing Infinite) :
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite := by
  sorry

theorem controls : TruthCore.Causality.ReceptionLimitation.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ReceptionLimitation
