import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

universe u v

namespace TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseFromUnion
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-- Every composite has a cause, other than itself, of its being, derived from
five premises. A composite has two distinct components (q.11 a.1); distinct
components of one thing are united only by a uniting cause (q.3 a.7, third
proof); a uniting cause efficiently causes what it unites in some respect (q.3
a.7, third proof); a uniting cause causes the being of what it unites (q.11 a.1
with q.3 a.7); and nothing is an efficient cause of itself (q.2 a.3, second
way). The uniter causes the composite's being, and it is not the composite,
since otherwise the composite would efficiently cause itself. -/
theorem compositeHasAUnitingCause {Being : Sort u} {Respect : Sort v}
    (Composite : Being → Prop) (ComponentOf : Being → Being → Prop)
    (Unites : Being → Being → Being → Being → Prop)
    (EfficientlyCausesIn CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite ComponentOf)
    (hUnite : DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites)
    (hEfficient : UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn)
    (hBeing : UnitingCauseCausesBeingReading Unites CausesIn esse)
    (hNoSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) :
    CompositeHasAUnitingCauseReading Composite CausesIn esse :=
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseFromUnion
