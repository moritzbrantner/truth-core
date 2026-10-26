import TruthCore.Greek.Plato.Timaeus
import TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter13
namespace TruthCore.Results.Bridges.ScgInnovatingCauseTimaeusDistinctCause
open TruthCore.Greek.Plato.Timaeus
open TruthCore.Latin.Aquinas.SummaContraGentiles
/-- Bridge (#401), a transcription (invariant 16): the *Summa contra Gentiles*
I.13 premise that whatever comes to be anew has an innovating cause other than
itself (`STMT-WHAT-COMES-TO-BE-ANEW-HAS-INNOVATING-CAUSE`) is the instance of the
Timaeus distinct-cause schema, *Timaeus* 28a (`STMT-CAUSE-PRINCIPLE-DISTINCT`),
in which "comes to be" is read as "comes to be anew" (`ComesToBeAnew`: is after
not being, or began with time) and "causes" as "causes the origin of". The proof
is the premise. It does not say that Plato's "comes to be" means temporal
beginning (`DISAMB-COMING-TO-BE`): only that the SCG principle is one reading of
the Timaeus schema, so the Timaeus results apply to it. -/
theorem distinctCausePrincipleOfInnovatingCause {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop)
    (BeganWithTime : Being → Prop) (CausesOrigin : Being → Being → Prop)
    (hInnovating : WhatComesToBeAnewHasInnovatingCauseReading
      IsAt Before BeganWithTime CausesOrigin) :
    DistinctCausePrinciple (ComesToBeAnew IsAt Before BeganWithTime) CausesOrigin :=
  hInnovating
end TruthCore.Results.Bridges.ScgInnovatingCauseTimaeusDistinctCause
