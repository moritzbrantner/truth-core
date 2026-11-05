import TruthCore.Latin.Aquinas.DeEnte.EsseReception
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

universe u w

namespace TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityFromReception
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- What is its own esse is infinite, derived from four reception readings:
limited esse is received (q.7 a.1), received esse is received in the thing's own
essence (De ente c.4), a receiver is not the esse it receives (De ente c.3), and
unlimited esse is infinite (q.7 a.1-2). If x's esse were limited it would be
received in some r; r is x's essence, which equals x's esse, so x's esse would
be received in itself. Hence x's esse is unlimited and x is infinite. -/
theorem subsistentBeingIsInfinite {Being : Sort u} {Principle : Sort w}
    (essenceOf esseOf : Being → Principle) (Infinite EsseLimited : Being → Prop)
    (EsseReceivedIn : Being → Principle → Prop)
    (hOnly : EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn)
    (hNature : EsseReceivedInOwnEssenceReading essenceOf EsseReceivedIn)
    (hDistinct : ReceiverIsNotTheReceivedEsseReading esseOf EsseReceivedIn)
    (hInfinite : UnlimitedEsseIsInfiniteReading EsseLimited Infinite) :
    SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite :=
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityFromReception
