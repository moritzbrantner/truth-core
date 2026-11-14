import TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22SecondCase

namespace TruthCore.Results.Aquinas.SummaContraGentiles.Chapter22SecondCase

open TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction
open TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22SecondCase

set_option synthInstance.maxSize 4096

/-- Control (a), general form: with n.4's second case and n.2's per se clause,
an inseparable union of a per se necessary esse with a distinct q cannot
depend on q. The conclusion is the consequent of neither premise: it chains
both through the dependence definition of per se necessity. -/
theorem essence_dependent_inseparable_union_excluded (p : DependenceProfile W B P R) (w : W)
    (hSecond : InseparableEsseInheritsConjunctionSource p w)
    (hClause : DependenceOnAnotherGivesNecessityFromIt p) :
    EssenceDependentInseparableUnionExcludedAt p w := by
  sorry

/-- Both written n.4 cases in the dependence sense. The case split is on
intelligibility apart: the first case makes q accidental and so not the
quiddity; the second makes the esse depend absolutely on another, against
its per se necessity. Constructive: the second branch is reached through
`¬ conceivableApart`, obtained from the first. No modal proxy is used. -/
theorem dependent_conjunction_not_quiddity (p : DependenceProfile W B P R) (w : W)
    (hAccident : IntelligibleSeparationMakesAccidental p.toProfile)
    (hQuiddity : AccidentNotQuiddityOfEsseBearer p.toProfile)
    (hSecond : InseparableEsseInheritsConjunctionSource p w)
    (hClause : DependenceOnAnotherGivesNecessityFromIt p) :
    DependentConjunctionRejectedAsQuiddityAt p w := by
  sorry

/-- n.2 (coarsened coverage) composed with both n.4 cases: horns (i)/(ii)
either make the esse depend absolutely on another (n.2's clause) or make its
joining so depend (the n.4 theorem above); horn (iii) makes q accidental. -/
theorem joined_distinct_quiddity_rejected (p : DependenceProfile W B P R) (w : W)
    (hCoverage : JoinedDistinctTrilemmaCoverage p w)
    (hAccident : IntelligibleSeparationMakesAccidental p.toProfile)
    (hQuiddity : AccidentNotQuiddityOfEsseBearer p.toProfile)
    (hSecond : InseparableEsseInheritsConjunctionSource p w)
    (hClause : DependenceOnAnotherGivesNecessityFromIt p)
    (hHornThree : ConsequentOfEsseIsAccidental p) :
    JoinedDistinctQuiddityRejectedAt p w := by
  sorry

/-- n.6 composed with both n.4 cases, without n.2 coverage: a genuine quiddity
joined to the per se necessary esse which is not one per se with it has a
joining source that is not other than the esse itself. -/
theorem non_unified_quiddity_union_self_sourced (p : DependenceProfile W B P R) (w : W)
    (hUnion : NonUnifiedUnionHasSource p w)
    (hAccident : IntelligibleSeparationMakesAccidental p.toProfile)
    (hQuiddity : AccidentNotQuiddityOfEsseBearer p.toProfile)
    (hSecond : InseparableEsseInheritsConjunctionSource p w)
    (hClause : DependenceOnAnotherGivesNecessityFromIt p) :
    NonUnifiedQuiddityUnionSelfSourcedAt p w := by
  sorry

/-- Seven finite assignments on #1602's stable distinct profile: control (a)
and its per se clause omission, control (b) and its per se unity omission,
a self-sourced residual, a horn (iii) accident omission and a nonvacuous
positive case. Signature facts only. -/
theorem second_case_controls : SecondCaseControls := by
  sorry

end TruthCore.Results.Aquinas.SummaContraGentiles.Chapter22SecondCase
