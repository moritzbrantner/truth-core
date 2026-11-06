module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.InfinityFromIdentityScope
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- Frozen exact scope obligation; source claims and original Challenges remain unchanged. -/
theorem infinityFromIdentityScope (f : Frame) (Infinite EsseLimited : f.Being → Prop)
    (ReceptivePotencyTo : f.Principle → f.Principle → Prop)
    (hOnly : EsseLimitedOnlyThroughReceptionReading EsseLimited (f.Received f.selected))
    (hNature : IdentityScopedOwnEssence f)
    (hPotency : ReceiverInPotencyToReceivedEsseReading f.esseOf
      (f.Received f.selected) ReceptivePotencyTo)
    (hIrreflexive : NothingInReceptivePotencyToItself ReceptivePotencyTo)
    (hInfinite : UnlimitedEsseIsInfiniteReading EsseLimited Infinite) :
    SubsistentBeingIsInfiniteReading f.essenceOf f.esseOf Infinite := by
  have hRestricted :=
    TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityFromReception.subsistentBeingIsInfinite
      (Being := {x : f.Being // f.esseOf x = f.essenceOf x})
      (fun x => f.essenceOf x.val) (fun x => f.esseOf x.val)
      (fun x => Infinite x.val) (fun x => EsseLimited x.val)
      (fun x r => f.Received f.selected x.val r) ReceptivePotencyTo
      (fun x hx => hOnly x.val hx)
      (fun x r hr => hNature x.val r x.property hr)
      (fun x r hr => hPotency x.val r hr) hIrreflexive
      (fun x hx => hInfinite x.val hx)
  intro x hx
  exact hRestricted ⟨x, hx⟩ hx

end TruthCore.Results.Causality.EsseReceptionDefinitions.InfinityFromIdentityScope
