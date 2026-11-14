module

public import TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaContraGentiles.Chapter22Conjunction

open TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction

set_option synthInstance.maxSize 4096

/-- Non-transcription structural distinction: at the counterworld of the
conjunction the same represented esse principle still satisfies
`esseExistsAt`. This is a structural surrogate: bearer existence, q.3
actuality and q's existence at the counterworld are not tracked. It does
not use an opaque bridge from underivedness to essence–esse identity. -/
theorem necessary_esse_contingent_join_separates (p : Profile W B P R) (w : W) :
    NecessityAndContingentJoinSeparateAt p w := by
  intro e q hNecessary hContingent
  rcases hContingent with ⟨hJoined, v, hAccess, hNotJoined⟩
  exact ⟨hJoined, ⟨v, hAccess, hNecessary.2 v hAccess, hNotJoined⟩⟩

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
  intro x hNecessary hIdentified hContingent
  have hSeparated : ModalSeparationAt p w (p.q3.esseOf x) (p.proposedQuiddityOf x) :=
    necessary_esse_contingent_join_separates p w
      (p.q3.esseOf x) (p.proposedQuiddityOf x) hNecessary hContingent
  exact hQuiddity x (p.proposedQuiddityOf x) hIdentified
    (hAccident (p.q3.esseOf x) (p.proposedQuiddityOf x)
      (hFromWorld (p.q3.esseOf x) (p.proposedQuiddityOf x) hSeparated))

/-- Each finite omission is a counterexample to the larger attributed
inference with that exact bridge withheld, not a metaphysical refutation of
the bridge. The stable distinct-union profile limits the reach of the first
n.4 case, relative to the modal proxy; n.4's second case is not encoded. -/
theorem controls : Controls := by
  dsimp [Controls, NecessaryEsseAt, ContingentConjunctionAt, ModalSeparationAt,
    WorldSeparationShowsIntelligibilityAt, IntelligibleSeparationMakesAccidental,
    AccidentNotQuiddityOfEsseBearer, ContingentReplyPremisesAt,
    contingentProfile, noIntelligibilityProfile, noAccidentBridgeProfile,
    noQuiddityCriterionProfile, nonEsseBearerProfile, noNecessaryEsseProfile,
    necessaryDistinctProfile]
  decide

/-- Finite boundary on the D → E root-route question: exact actual
underivedness from the existing interface does not by itself fix the q.3
represented principle identity, even with the first n.4 case's premises.
The bare non-entailment is already in `UnderivedEssenceEsse.Controls`. -/
theorem underived_distinct_boundary : UnderivedDistinctBoundary := by
  dsimp [UnderivedDistinctBoundary, stableDistinctOntic, stableDistinctSupport,
    NecessaryEsseAt, ModalSeparationAt, ContingentReplyPremisesAt,
    WorldSeparationShowsIntelligibilityAt, IntelligibleSeparationMakesAccidental,
    AccidentNotQuiddityOfEsseBearer, necessaryDistinctProfile, contingentProfile,
    TruthCore.Causality.NecessarilyUnderived.NoExistingSupportAt,
    TruthCore.German.Kant.CosmologicalInference.NecessaryAt,
    TruthCore.Causality.ActualUnderivedEssenceEsse.ActualUnderivedEssenceIdentity]
  decide

end TruthCore.Results.Aquinas.SummaContraGentiles.Chapter22Conjunction
