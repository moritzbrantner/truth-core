import TruthCore.Latin.Aquinas.DeEnte.EsseReception
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-!
Formal omission and compatibility controls for the four reception readings
that derive `SubsistentBeingIsInfiniteReading` (result
SUBSISTENT-INFINITY-FROM-RECEPTION). Each control is a stipulated finite
interpretation of the shared vocabulary. It shows what the encoded premises do
and do not entail; it is not a claim that any interpretation is metaphysically
possible or that a rival reading of Aquinas is correct.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.Control
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- Some interpretation satisfies the three listed readings and the conclusion
`SubsistentBeingIsInfiniteReading` fails in it. Each case below fixes which of
the four readings is omitted, and the other three hold. -/
def Certificate : Prop :=
  -- 1. Without limitation-only-through-reception: a limited, unreceived esse.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop),
    ¬ EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedInOwnEssenceReading essenceOf EsseReceivedIn ∧
    ReceiverIsNotTheReceivedEsseReading esseOf EsseReceivedIn ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 2. Without reception-in-own-essence: esse received in a foreign principle.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    ¬ EsseReceivedInOwnEssenceReading essenceOf EsseReceivedIn ∧
    ReceiverIsNotTheReceivedEsseReading esseOf EsseReceivedIn ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 3. Without receiver/received distinctness: an esse received in itself.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedInOwnEssenceReading essenceOf EsseReceivedIn ∧
    ¬ ReceiverIsNotTheReceivedEsseReading esseOf EsseReceivedIn ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 4. Without unlimited-esse-is-infinite: nothing limited, nothing infinite.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedInOwnEssenceReading essenceOf EsseReceivedIn ∧
    ReceiverIsNotTheReceivedEsseReading esseOf EsseReceivedIn ∧
    ¬ UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    ¬ SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) ∧
  -- 5. All four readings together, with a being whose esse differs from its
  -- essence, is received in that essence, is limited and is not infinite.
  (∃ (B P : Type) (essenceOf esseOf : B → P) (Infinite EsseLimited : B → Prop)
      (EsseReceivedIn : B → P → Prop),
    EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn ∧
    EsseReceivedInOwnEssenceReading essenceOf EsseReceivedIn ∧
    ReceiverIsNotTheReceivedEsseReading esseOf EsseReceivedIn ∧
    UnlimitedEsseIsInfiniteReading EsseLimited Infinite ∧
    (∃ x, esseOf x = essenceOf x) ∧
    (∃ y, esseOf y ≠ essenceOf y ∧ EsseReceivedIn y (essenceOf y) ∧
      EsseLimited y ∧ ¬ Infinite y))

end TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.Control
