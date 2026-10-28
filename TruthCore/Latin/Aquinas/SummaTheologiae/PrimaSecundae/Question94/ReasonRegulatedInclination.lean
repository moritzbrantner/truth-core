/-! Bounded reading of the full materialized ST I-II q.94 a.2, especially ad 2.
It qualifies, rather than identifies with moral authority, appeal to natural
inclination. No source-level inference is proved by the declaration. -/
namespace TruthCore.Latin.Aquinas.SummaTheologiae

/-- Inclinations of parts of human nature, including concupiscible and
irascible appetite, pertain to natural law insofar as regulated by reason.
Only the sufficient direction is recorded. `RegulatedByReason` is an open
substantive condition, not defined as whatever someone presently wants or
whatever conforms to natural law. This statement does not imply that every
actual inclination is to be followed, or give a criterion for correct reason.
Source: ST I-II q.94 a.2 ad 2.
-/
def ReasonRegulatedInclinationsBelongToNaturalLawReading {Inclination : Sort u}
    (HumanNaturalInclination RegulatedByReason PertainsToNaturalLaw : Inclination → Prop) : Prop :=
  ∀ i, HumanNaturalInclination i → RegulatedByReason i → PertainsToNaturalLaw i

end TruthCore.Latin.Aquinas.SummaTheologiae
