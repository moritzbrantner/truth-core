import TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction

namespace TruthCore.Results.Aquinas.SummaContraGentiles.Chapter22Conjunction

open TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction

/-- Non-transcription structural distinction: the counterworld of the
conjunction still contains the *same esse*. In particular, this theorem does
not use an opaque bridge from underivedness to essence–esse identity. -/
theorem necessary_esse_contingent_join_separates (p : Profile W B P R) (w : W) :
    NecessityAndContingentJoinSeparateAt p w := by
  sorry

/-- Explicit *conditional transcription of n.4's interpretive steps*,
consuming the genuinely structural separation lemma above. The three OPEN
premises are not a proof that their metaphysical interpretations are true.
The conclusion rejects q as the quiddity of the identified esse bearer; it
does not assert q = e or that every underived being has this identity. -/
theorem contingent_join_not_first_quiddity (p : Profile W B P R) (w : W)
    (hFromWorld : WorldSeparationShowsIntelligibilityAt p w)
    (hAccident : IntelligibleSeparationMakesAccidental p)
    (hQuiddity : AccidentNotQuiddityOfEsseBearer p) :
    ContingentConjunctionRejectedAsQuiddityAt p w := by
  sorry

/-- Each finite omission is a counterexample to the larger attributed
inference with that exact bridge withheld, not a metaphysical refutation of
the bridge. The stable distinct-union profile limits n.3–4's reach. -/
set_option synthInstance.maxSize 4096 in
theorem controls : Controls := by
  sorry

/-- Finite boundary on the D → E root-route question: exact actual
underivedness from the existing interface does not by itself fix the q.3
represented principle identity, even with the n.3–4 reply premises. -/
set_option synthInstance.maxSize 4096 in
theorem underived_distinct_boundary : UnderivedDistinctBoundary := by
  sorry

end TruthCore.Results.Aquinas.SummaContraGentiles.Chapter22Conjunction
