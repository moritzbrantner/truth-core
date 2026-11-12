import TruthCore.Causality.PerfectionTransferGrounding
import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution

/-! A grounded entry into the perfection-transfer support cycle: unrestricted
transfer from universal-scope transfer, nonuniversal transfer, no self-causation of
esse and excluded middle; and its controls. Analyst formulations, attribution
deferred. No premise is established. -/

namespace TruthCore.Results.Causality.PerfectionTransferGrounding

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.PerfectionTransferGrounding
open TruthCore.Causality.PerfectionTransferGrounding.Control
open TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer
open TruthCore.Logic

/-- If c causes x's esse and x is in act in r, then either c causes the esse of
every other actual being or it does not (excluded middle). x is not c, since
nothing causes its own esse. In the first case universal-scope transfer gives that
c causes x's being in act in r; in the second, nonuniversal transfer does. -/
theorem causeOfBeingCausesEveryPerfectionGrounded {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hEM : ExcludedMiddle)
    (hUniv : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNon : NonuniversalPerfectionTransfer InAct CausesIn esse)
    (hOwn : NothingCausesItsOwnBeing CausesIn esse) :
    CauseOfBeingCausesEveryPerfection InAct CausesIn esse := by
  sorry

attribute [local instance] transferFourForallDecidable

theorem controls : Control.Controls := by
  sorry

end TruthCore.Results.Causality.PerfectionTransferGrounding
