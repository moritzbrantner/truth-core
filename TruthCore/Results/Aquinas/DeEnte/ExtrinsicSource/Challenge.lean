import TruthCore.Latin.Aquinas.DeEnte.ExtrinsicSource
import TruthCore.Causality.TermSenseForks2
import TruthCore.Case.Catholicism.CauseOfBeingHasBeing

/-!
# De ente: from distinct esse to an extrinsic source (#1629)

Conditional derivations for the *De ente* c.3 [69874] inference (Baur/Koch
numbering; Leonine c.4). The extra premise that turns
"not self-caused" into "caused by another" is `DistinctEsseHasSomeCause`
(every actual distinct esse has some cause of being). In De ente's vocabulary
it comes from `DistinctEsseNatureOrOtherCause` (esse only, distinct-esse
beings only, nature disjunct in the efficient sense `NATURE_SOURCE_2`) and the
self-causation reading. The weak exhaustiveness is derived from the
literal De ente disjunction (`NATURE_SOURCE_1`, every respect) only through
the open sense bridge `NatureSourcedDistinctEsseIsEfficient`; the
`FormalNatureControl` interpretation shows that without that bridge the literal
disjunction and the rejection of efficient self-causation give no other
cause. The conclusion `DistinctEsseHasOtherActualCause` is a mode-unspecified
cause of being other than x (`c ≠ x`, not non-constituency) and in act as to
being; it is not the q.3 a.4 efficient-cause statement, and no bridge to that
statement is registered. None of the premises is proved here.
-/

namespace TruthCore.Results.Aquinas.DeEnte.ExtrinsicSource

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (CauseOfBeingInActAsToBeing)

/-- The De ente decomposition of the extra premise: the weak exhaustiveness
and the self-causation reading give every actual distinct-esse being some
cause of its esse (its own self, on the quiddity horn). -/
theorem distinctEsseCausedFromDeEnte (p : Profile B P R) (n : NatureSource B R)
    (hExhaustive : DistinctEsseNatureOrOtherCause p n)
    (hSelf : QuiddityCausingEsseIsSelfCausationReading p n) :
    DistinctEsseHasSomeCause p := by
  sorry

/-- From "caused" to "caused by another". For an actual x with esse other than
its essence, some c causes x's esse; c is not x, by no-self-causation; c is in
act as to being. The cause is mode-unspecified: nothing here makes it
efficient, so the conclusion is not the q.3 a.4 efficient-cause statement. -/
theorem distinctEsseOtherCauseFromCaused (p : Profile B P R)
    (hCaused : DistinctEsseHasSomeCause p)
    (hNoSelf : NothingCausesItsOwnBeing p.CausesIn p.esse)
    (hInAct : CauseOfBeingInActAsToBeing p.InAct p.CausesIn p.esse) :
    DistinctEsseHasOtherActualCause p := by
  sorry

/-- The literal De ente disjunction, instantiated at esse for a distinct-esse
being and passed through the efficiency bridge, gives the weak exhaustiveness. -/
theorem distinctEsseExhaustionFromDeEnte (p : Profile B P R) (n : NatureSource B R)
    (hGeneral : NatureOrExtrinsicSourceReading p n)
    (hEfficient : NatureSourcedDistinctEsseIsEfficient p n) :
    DistinctEsseNatureOrOtherCause p n := by
  sorry

/-- The six finite interpretations on `Bool`. Explicit proof terms; no
`propext` from `simp`. -/
theorem extrinsicSourceControls : ExtrinsicSourceControls := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.ExtrinsicSource
