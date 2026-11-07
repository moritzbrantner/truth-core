module

public import TruthCore.Causality.ReceptionLimitation

@[expose] public section

namespace TruthCore.Results.Causality.ReceptionLimitation
open TruthCore.Causality.ReceptionLimitation
open TruthCore.Causality.EsseReceptionDefinitionFork (Frame IdentityScopedOwnEssence)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Latin.Aquinas.DeEnte (ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception
  (UnlimitedEsseIsInfiniteReading)
open TruthCore.Causality.WholePowerPerfection
open TruthCore.Causality.RootPurity (UnlimitedDeterminationsArePure)
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)

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
  intro x hx
  have hNone : ∀ r, ¬ f.Received f.selected x r := by
    intro r hr
    have hDistinct : f.esseOf x ≠ f.essenceOf x := by
      intro hEq
      have hRecipient : r = f.essenceOf x := hNature x r hEq hr
      have hp : ReceptivePotencyTo r (f.esseOf x) := hPotency x r hr
      rw [hRecipient, hEq] at hp
      exact hIrreflexive (f.essenceOf x) hp
    exact hx (Or.inr (Or.inl hDistinct))
  exact hUnreceived x hNone

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
  intro x hx d hd
  have hOwn : OwnBeing x := unlimitedIsOwnBeing f Composite PriorSimply OwnBeing
    ReceptivePotencyTo hNature hPotency hIrreflexive hUnreceived x hx
  have hNotRecipient : ¬ Recipient x := hNoRecipient x hOwn
  exact hPure x hNotRecipient d hd

/-- Shared step: an unlimited esse is received in nothing (q.7 a.2), so its
bearer is its own being (q.7 a.1). -/
theorem ownBeingOfUnlimitedEsse {B P : Type} (EsseLimited OwnBeing : B → Prop)
    (EsseReceivedIn : B → P → Prop)
    (hContracted : ReceivedEsseIsLimited EsseLimited EsseReceivedIn)
    (hUnreceived : UnreceivedEsseIsOwnBeing EsseReceivedIn OwnBeing) :
    ∀ x, ¬ EsseLimited x → OwnBeing x :=
  fun x hx => hUnreceived x (fun r hr => hx (hContracted x r hr))

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
  intro x hx d hd
  have hOwn : OwnBeing x :=
    ownBeingOfUnlimitedEsse EsseLimited OwnBeing EsseReceivedIn hContracted hUnreceived x
      (hInfinite x hx)
  exact hWhole x hOwn d (hPertain d hd)

/-- Second derivation of the q.7 a.1 leaf: an unlimited esse is not received
(q.7 a.2), so its bearer is its own being (q.7 a.1), which is infinite (q.7 a.1
with own being as the primitive). -/
theorem unlimitedEsseIsInfinite {B P : Type}
    (EsseLimited Infinite OwnBeing : B → Prop) (EsseReceivedIn : B → P → Prop)
    (hContracted : ReceivedEsseIsLimited EsseLimited EsseReceivedIn)
    (hUnreceived : UnreceivedEsseIsOwnBeing EsseReceivedIn OwnBeing)
    (hOwnInfinite : OwnBeingIsInfinite OwnBeing Infinite) :
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite := by
  intro x hx
  have hOwn : OwnBeing x :=
    ownBeingOfUnlimitedEsse EsseLimited OwnBeing EsseReceivedIn hContracted hUnreceived x hx
  exact hOwnInfinite x hOwn

/-- A being whose represented esse is its essence, that is not composite and to
which nothing is prior, has no represented limiting principle. -/
theorem noLimitingPrinciple (f : Frame) (x : f.Being) (hEq : f.esseOf x = f.essenceOf x)
    (Composite : f.Being → Prop) (hComposite : ¬ Composite x)
    (PriorSimply : f.Being → f.Being → Prop) (hPrior : ∀ y, ¬ PriorSimply y x) :
    ¬ HasLimitingPrinciple Composite PriorSimply f.essenceOf f.esseOf x :=
  fun h => h.elim hComposite (fun h => h.elim (fun hne => hne hEq)
    (fun h => Exists.elim h (fun y hy => hPrior y hy.2)))

open TruthCore.Causality.ReceptionLimitation.Control in
theorem controls : TruthCore.Causality.ReceptionLimitation.Control.Certificate := by
  have uNo := noLimitingPrinciple noRec () rfl no1 id no2 (fun _ h => h)
  have uOwn := noLimitingPrinciple ownRec () rfl no1 id no2 (fun _ h => h)
  have uOther := noLimitingPrinciple otherRec () rfl no1 id no2 (fun _ h => h)
  have noRecInputs : OwnInputs noRec potNone yes1 :=
    ⟨fun _ _ _ hr => False.elim hr, fun _ _ hr => False.elim hr, fun _ h => h,
      fun _ _ => trivial⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ _ _ hr => False.elim hr, fun _ _ hr => False.elim hr, fun _ h => h,
      fun h => h () (fun _ hr => hr), fun h => h () uNo, fun _ h _ => h,
      fun _ h => False.elim (h trivial), fun h => h () uNo () trivial⟩
  · exact ⟨fun _ _ _ hr => hr, fun _ _ _ => trivial, fun h => h false trivial,
      fun _ h => h false rfl, fun h => h () uOwn, fun _ h _ => h,
      fun _ h => False.elim (h trivial), fun h => h () uOwn () trivial⟩
  · exact ⟨fun _ _ _ hr => hr, fun h => h () false rfl, fun _ h => h,
      fun _ h => h false rfl, fun h => h () uOwn, fun _ h _ => h,
      fun _ h => False.elim (h trivial), fun h => h () uOwn () trivial⟩
  · exact ⟨fun h => Bool.noConfusion (h () true rfl rfl), fun _ _ hr => ⟨hr, rfl⟩,
      fun _ h => Bool.noConfusion (h.1.symm.trans h.2),
      fun _ h => h true rfl, fun h => h () uOther, fun _ h _ => h,
      fun _ h => False.elim (h trivial), fun h => h () uOther () trivial⟩
  · exact ⟨noRecInputs, fun _ _ => trivial⟩
  · exact ⟨noRecInputs, fun h => h () trivial trivial, fun _ h => False.elim (h trivial),
      fun h => h () uNo () trivial⟩
  · exact ⟨noRecInputs, fun _ _ h => h, fun h => h () (fun h => h) () trivial,
      fun h => h () uNo () trivial⟩
  · exact ⟨noRecInputs, fun _ _ h => h, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
  · exact ⟨fun h => h () trivial trivial, fun _ _ _ => trivial, fun _ h => h () trivial,
      fun _ h => False.elim h, fun _ _ => trivial, fun h => h () trivial () trivial⟩
  · exact ⟨fun _ _ h => h, fun h => h () () trivial, fun _ h => h () trivial,
      fun _ h => False.elim h, fun _ _ => trivial, fun h => h () trivial () trivial⟩
  · exact ⟨fun _ _ h => h, fun _ _ h => h, fun h => h () (fun _ h => h),
      fun _ h => False.elim h, fun _ _ => trivial, fun h => h () trivial () trivial⟩
  · exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ => trivial,
      fun h => h () trivial () trivial, fun _ _ => trivial, fun h => h () trivial () trivial⟩
  · exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ => trivial, fun _ _ _ h => h,
      fun h => h () trivial, fun h => h () trivial () trivial⟩
  · exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ => trivial, fun _ _ _ _ => trivial,
      fun _ _ => trivial, fun _ _ _ _ => trivial⟩
  · exact ⟨fun h => h () () trivial, fun _ h => h () trivial, fun _ h => h,
      fun h => h () (fun h => h)⟩
  · exact ⟨fun _ _ h => h, fun h => h () (fun _ h => h), fun _ h => h,
      fun h => h () (fun h => h)⟩
  · exact ⟨fun _ _ h => h, fun _ _ => trivial, fun h => h () trivial,
      fun h => h () (fun h => h)⟩
  · exact ⟨fun _ _ h => h, fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

end TruthCore.Results.Causality.ReceptionLimitation
