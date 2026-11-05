import TruthCore.Causality.EsseReception
import TruthCore.Latin.Aquinas.DeEnte.EsseReception
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-!
Formal omission and compatibility controls for the five reception premises
that derive `SubsistentBeingIsInfiniteReading` (result
SUBSISTENT-INFINITY-FROM-RECEPTION). Each control is a stipulated finite
interpretation of the shared vocabulary. It shows what the encoded premises do
and do not entail. It does not claim that any interpretation is metaphysically
possible or that a rival reading of Aquinas is correct.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.Control
open TruthCore.Causality.EsseReception
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- For each of the five premises, some interpretation satisfies the other four
while that premise and `SubsistentBeingIsInfiniteReading` both fail. A sixth
interpretation satisfies all five, non-vacuously. -/
def Certificate : Prop :=
  -- 1. Without limitation-only-through-reception: a limited, unreceived esse.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop) (ReceptivePotencyTo : P → P → Prop),
    ¬ EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedOnlyInOwnEssence essenceOf EsseReceivedIn ∧
    ReceiverInPotencyToReceivedEsseReading esseOf EsseReceivedIn ReceptivePotencyTo ∧
    NothingInReceptivePotencyToItself ReceptivePotencyTo ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 2. Without reception-only-in-own-essence: esse received in a foreign principle.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop) (ReceptivePotencyTo : P → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    ¬ EsseReceivedOnlyInOwnEssence essenceOf EsseReceivedIn ∧
    ReceiverInPotencyToReceivedEsseReading esseOf EsseReceivedIn ReceptivePotencyTo ∧
    NothingInReceptivePotencyToItself ReceptivePotencyTo ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 3. Without receiver-in-potency: an esse received in itself, with no potency.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop) (ReceptivePotencyTo : P → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedOnlyInOwnEssence essenceOf EsseReceivedIn ∧
    ¬ ReceiverInPotencyToReceivedEsseReading esseOf EsseReceivedIn ReceptivePotencyTo ∧
    NothingInReceptivePotencyToItself ReceptivePotencyTo ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 4. Without no-self-potency: an esse received in itself and in potency to itself.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop) (ReceptivePotencyTo : P → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedOnlyInOwnEssence essenceOf EsseReceivedIn ∧
    ReceiverInPotencyToReceivedEsseReading esseOf EsseReceivedIn ReceptivePotencyTo ∧
    ¬ NothingInReceptivePotencyToItself ReceptivePotencyTo ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 5. Without unlimited-esse-is-infinite: nothing limited, nothing infinite.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop) (ReceptivePotencyTo : P → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedOnlyInOwnEssence essenceOf EsseReceivedIn ∧
    ReceiverInPotencyToReceivedEsseReading esseOf EsseReceivedIn ReceptivePotencyTo ∧
    NothingInReceptivePotencyToItself ReceptivePotencyTo ∧
    ¬ UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 6. All five premises together, with a being whose esse is its essence and a
  -- being whose esse differs from its essence, is received in that essence, is
  -- limited and is not infinite.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop) (ReceptivePotencyTo : P → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedOnlyInOwnEssence essenceOf EsseReceivedIn ∧
    ReceiverInPotencyToReceivedEsseReading esseOf EsseReceivedIn ReceptivePotencyTo ∧
    NothingInReceptivePotencyToItself ReceptivePotencyTo ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    (∃ x, esseOf x = essenceOf x) ∧
    (∃ y, esseOf y ≠ essenceOf y ∧ EsseReceivedIn y (essenceOf y) ∧
      EsseLimited y ∧ ¬ Infinite y))

end TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.Control
