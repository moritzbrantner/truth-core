module

public import TruthCore.Causality.EsseReception
public import TruthCore.Latin.Aquinas.DeEnte.EsseReception
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

@[expose] public section

universe u w

namespace TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityFromReception
open TruthCore.Causality.EsseReception
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- What is its own esse is infinite, derived from five reception premises.
Three are sourced: limited esse is received (q.7 a.1), a receiver is in
receptive potency to the esse it receives (De ente c.3), and unlimited esse is
infinite (q.7 a.1-2). Two are unattributed: received esse is received only in
the thing's own essence, and nothing is in receptive potency to itself.
If x's esse were limited, it would be received in some r. Then r is x's
essence, which equals x's esse, so x's esse would be in receptive potency to
itself. Hence x's esse is unlimited and x is infinite. -/
theorem subsistentBeingIsInfinite {Being : Sort u} {Principle : Sort w}
    (essenceOf esseOf : Being → Principle) (Infinite EsseLimited : Being → Prop)
    (EsseReceivedIn : Being → Principle → Prop)
    (ReceptivePotencyTo : Principle → Principle → Prop)
    (hOnly : EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn)
    (hNature : EsseReceivedOnlyInOwnEssence essenceOf EsseReceivedIn)
    (hPotency : ReceiverInPotencyToReceivedEsseReading esseOf EsseReceivedIn ReceptivePotencyTo)
    (hIrreflexive : NothingInReceptivePotencyToItself ReceptivePotencyTo)
    (hInfinite : UnlimitedEsseIsInfiniteReading EsseLimited Infinite) :
    SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite := by
  intro x hIdentity
  apply hInfinite x
  intro hLimited
  obtain ⟨r, hReceived⟩ := hOnly x hLimited
  have hSelf : r = esseOf x := (hNature x r hReceived).trans hIdentity.symm
  have hPot := hPotency x r hReceived
  rw [hSelf] at hPot
  exact hIrreflexive (esseOf x) hPot

end TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityFromReception
