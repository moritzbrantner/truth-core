import Mathlib
import TruthCore.German.Kant.CosmologicalInference

/-!
# Possible external causes versus brute contingent beginnings

Analyst-defined tests informed by the open questions in #505 and #492.
They are NOT source-derived claims about Pruss, Rasmussen or the
necessarybeing.com survey. Primary sources require independent witness
materialization before an attributed corpus claim is entered.

The modal causal *opportunity* premise is weaker than the unrestricted
PSR: an actual beginning can remain uncaused, provided an analogous
beginning could be externally caused in some accessible history.

The result does not, however, establish the metaphysical possibility of
the required externally caused history. It also does not exclude brute
contingent individuals coexisting with a necessary concrete being.

Worlds are complete histories. 'beginsContingency' is an independently
interpreted predicate, not a temporal transition or a proof that the
totality of contingent things could have a first occurrence.
-/

namespace TruthCore.Causality.PossibleCauseOfContingency

open TruthCore.German.Kant.CosmologicalInference

/-- Modal setting, stipulated concreteness, a beginning of the state that
there are contingent concreta, and a typed state-of-affairs causal relation.
The latter is deliberately NOT conflated with individual-to-individual
`ontic.Causes`; causation of a totality need not cause each member. -/
structure Scenario (World Being : Type) where
  ontic : Ontic World Being
  concrete : Being → Prop
  beginsContingency : World → Prop
  causesContingencyTotality : World → Being → Prop

/-- A first occurrence of some contingent concrete reality, relative to
the supplied 'begins' predicate. The beginning is NOT deduced simply from
existence of contingent individuals. -/
def ContingencyBeginsAt (s : Scenario W B) (w : W) : Prop :=
  s.beginsContingency w ∧
  ∃ x, s.concrete x ∧ ContingentAt s.ontic w x

/-- A concrete individual is external to the totality of contingent
concrete individuals if it is distinct from every member. 'External' does
not itself specify causal powers or sufficiency of an explanation. -/
def OutsideContingentTotalityAt (s : Scenario W B) (w : W) (c : B) : Prop :=
  ∀ x, s.concrete x → ContingentAt s.ontic w x → x ≠ c

/-- The contentious existential opportunity: in an accessible history
the contingent totality begins and has an *existing concrete* source
which is outside its members. An abstract or nonexistent reason cannot
serve as the required bearer. -/
def PossiblyExternallyCausedAt (s : Scenario W B) (w : W) : Prop :=
  ∃ v, s.ontic.frame.access w v ∧ ContingencyBeginsAt s v ∧
    ∃ c, s.concrete c ∧ s.ontic.ExistsAt v c ∧
      s.causesContingencyTotality v c ∧
      OutsideContingentTotalityAt s v c

/-- The independent modal possibility that the totality of contingent
concrete existence has a beginning in some accessible history. -/
def PossiblyBeginsAt (s : Scenario W B) (w : W) : Prop :=
  ∃ v, s.ontic.frame.access w v ∧ ContingencyBeginsAt s v

/-- Restricted modal causal opportunity: if the totality can begin, an
externally caused such beginning is accessible. Unlike actual PSR, it
does not require the actual beginning to be caused. It remains a
substantive metaphysical principle, especially at the totality case. -/
def CausalOpportunityAt (s : Scenario W B) (w : W) : Prop :=
  PossiblyBeginsAt s w → PossiblyExternallyCausedAt s w

/-- Every world is accessible from every world. This is stronger than
equivalence-frame S5 globally, but is sufficient for the small models.
No temporal relation is intended. -/
def UniversalFrame (s : Scenario W B) : Prop :=
  ∀ w v, s.ontic.frame.access w v

/-- Exactly the modal existence conclusion under consideration.
The same rigid individual is concrete and exists actually and at all
accessible worlds; it is not thereby God, simple, or causally sufficient. -/
def NecessaryConcreteAt (s : Scenario W B) (w : W) : Prop :=
  ∃ c, s.concrete c ∧ s.ontic.ExistsAt w c ∧ NecessaryAt s.ontic w c

/-- Purely external *candidate* existence, with no causal or first-beginning
claim. This is useful for auditing whether 'external' hides a necessary
being as an assumed possibility. -/
def ExternalCandidateAt (s : Scenario W B) (w : W) : Prop :=
  ∃ c, s.concrete c ∧ s.ontic.ExistsAt w c ∧
    OutsideContingentTotalityAt s w c

/-- Crucial scope audit. Under classical logic the mere existence of an
actual concrete individual external to *all contingent concreta* is
equivalent to an actual necessary concrete individual at that world.
The causal relation and the beginning predicate do no work here. -/
theorem externalCandidateIffNecessary
    (s : Scenario W B) (w : W) :
    ExternalCandidateAt s w ↔ NecessaryConcreteAt s w := by
  classical
  constructor
  · rintro ⟨c, hc, he, hOutside⟩
    refine ⟨c, hc, he, ?_⟩
    intro v hv
    by_cases heV : s.ontic.ExistsAt v c
    · exact heV
    · have hCont : ContingentAt s.ontic w c :=
        ⟨he, ⟨v, hv, heV⟩⟩
      exact False.elim ((hOutside c hc hCont) rfl)
  · rintro ⟨c, hc, he, hNec⟩
    refine ⟨c, hc, he, ?_⟩
    intro x _ hCont hEq
    subst x
    rcases hCont with ⟨_, v, hv, hAbsent⟩
    exact hAbsent (hNec v hv)

/-- Possible external causation of the *entire contingent totality*
entails an actual rigid necessary concrete being under universal modal
accessibility. Importantly, the formal argument uses the source's
externality; the independent philosophical work is defending its
possible causal availability, not the Lean implication. -/
theorem possibleExternalCauseYieldsNecessary
    (s : Scenario W B) (w : W)
    (hUniversal : UniversalFrame s)
    (hPossible : PossiblyExternallyCausedAt s w) :
    NecessaryConcreteAt s w := by
  rcases hPossible with ⟨v, _, _, c, hc, he, _, hOutside⟩
  have hAtV : NecessaryConcreteAt s v :=
    (externalCandidateIffNecessary s v).mp ⟨c, hc, he, hOutside⟩
  rcases hAtV with ⟨c, hc, _, hNecV⟩
  refine ⟨c, hc, hNecV w (hUniversal v w), ?_⟩
  intro u _
  exact hNecV u (hUniversal v u)

/-- The candidate non-PSR route: the possible-beginning premise and
restricted *possible*-causal-opportunity principle yield a de re necessary
concretum when modal accessibility is universal. These are two
unestablished metaphysical antecedents, not theorem-level truths. -/
theorem causalOpportunityAndPossibleBeginning
    (s : Scenario W B) (w : W)
    (hUniversal : UniversalFrame s)
    (hPossibleBeginning : PossiblyBeginsAt s w)
    (hOpportunity : CausalOpportunityAt s w) :
    NecessaryConcreteAt s w :=
  possibleExternalCauseYieldsNecessary s w hUniversal
    (hOpportunity hPossibleBeginning)

/-- Brute-only model: each of two mutually accessible worlds contains
exactly one different contingent concrete individual. The stipulated
beginning holds, but there is no possible external concrete totality
cause and no de re necessarily existing concrete individual. -/
def bruteOnly : Scenario Bool Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => w = x
    Causes := fun _ _ _ => False
  }
  concrete := fun _ => True
  beginsContingency := fun _ => True
  causesContingencyTotality := fun _ _ => False

theorem bruteOnlyUniversal : UniversalFrame bruteOnly := by
  intro _ _
  trivial

theorem bruteOnlyPossibleBeginning :
    PossiblyBeginsAt bruteOnly false := by
  refine ⟨false, True.intro, True.intro, false, True.intro, ?_⟩
  refine ⟨rfl, ⟨true, True.intro, ?_⟩⟩
  simp [bruteOnly]

theorem bruteOnlyNoExternalCause :
    ¬ PossiblyExternallyCausedAt bruteOnly false := by
  intro h
  rcases h with ⟨v, _, _, c, _, _, hc, _⟩
  exact hc

theorem bruteOnlyNoNecessary :
    ¬ NecessaryConcreteAt bruteOnly false := by
  intro h
  rcases h with ⟨c, _, he, hn⟩
  cases c with
  | false =>
      have ht := hn true True.intro
      cases ht
  | true =>
      cases he

/-- The causal-opportunity premise cannot be derived from the rest of
the brute-only modal model. This does not independently certify any
of its histories as metaphysically possible. -/
theorem bruteOnlyRejectsOpportunity :
    PossiblyBeginsAt bruteOnly false ∧
    ¬ CausalOpportunityAt bruteOnly false ∧
    ¬ NecessaryConcreteAt bruteOnly false := by
  exact ⟨bruteOnlyPossibleBeginning,
    (fun h => bruteOnlyNoExternalCause (h bruteOnlyPossibleBeginning)),
    bruteOnlyNoNecessary⟩

/-- Mixed rival: the same rigid `none` bearer exists in both histories,
with distinct contingent concreta `some false` and `some true`.
The necessary bearer causes the contingent totality only at world false.
At world true the contingent concrete root is *not* caused by anyone. -/
def mixed : Scenario Bool (Option Bool) where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x =>
      match x with
      | none => True
      | some b => w = b
    Causes := fun w c e =>
      w = false ∧ c = none ∧ e = some false
  }
  concrete := fun _ => True
  beginsContingency := fun _ => True
  causesContingencyTotality := fun w c =>
    w = false ∧ c = none

theorem mixedUniversal : UniversalFrame mixed := by
  intro _ _
  trivial

theorem mixedContingentAtFalse :
    ContingentAt mixed.ontic false (some false) := by
  refine ⟨rfl, ⟨true, True.intro, ?_⟩⟩
  simp [mixed]

theorem mixedContingentAtTrue :
    ContingentAt mixed.ontic true (some true) := by
  refine ⟨rfl, ⟨false, True.intro, ?_⟩⟩
  simp [mixed]

theorem mixedPossibleBeginning :
    PossiblyBeginsAt mixed false := by
  exact ⟨false, True.intro, True.intro, (some false),
    True.intro, mixedContingentAtFalse⟩

theorem mixedPossibleExternalCause :
    PossiblyExternallyCausedAt mixed false := by
  refine ⟨false, True.intro, ⟨True.intro,
      ⟨some false, True.intro, mixedContingentAtFalse⟩⟩,
    none, True.intro, True.intro, ⟨rfl, rfl⟩, ?_⟩
  intro x _ hCont hEq
  subst x
  rcases hCont with ⟨_, v, _, hAbsent⟩
  exact hAbsent True.intro

/-- A necessary concrete source is available at both worlds. -/
theorem mixedNecessaryConcrete : NecessaryConcreteAt mixed false := by
  exact ⟨none, True.intro, True.intro, fun _ _ => True.intro⟩

/-- Nonetheless one actual contingent concrete being is a causal root
in world true: no existing or nonexistent candidate causes it. -/
theorem mixedHasContingentUncausedRoot :
    ContingentAt mixed.ontic true (some true) ∧
    (∀ c, ¬ mixed.ontic.Causes true c (some true)) := by
  constructor
  · exact mixedContingentAtTrue
  · intro c h
    have hf : true = false := h.1
    cases hf

/-- The principle permits brute *actual* roots, even when a necessary
individual is present and an alternate externally caused beginning exists. -/
theorem causalOpportunityDoesNotExcludeBruteRoots :
    UniversalFrame mixed ∧
    PossiblyBeginsAt mixed false ∧
    CausalOpportunityAt mixed false ∧
    NecessaryConcreteAt mixed false ∧
    ContingentAt mixed.ontic true (some true) ∧
    (∀ c, ¬ mixed.ontic.Causes true c (some true)) := by
  rcases mixedHasContingentUncausedRoot with ⟨hCont, hUncaused⟩
  exact ⟨mixedUniversal, mixedPossibleBeginning,
    (fun _ => mixedPossibleExternalCause), mixedNecessaryConcrete,
    hCont, hUncaused⟩

/-- Presence of a necessary concrete bearer by itself does not yield
the possibility of externally causing the contingent totality:
that predicate remains a separate substantive causal requirement. -/
def noTotalityCause : Scenario Bool (Option Bool) :=
  { mixed with causesContingencyTotality := fun _ _ => False }

theorem necessaryBeingWithoutPossibleTotalityCause :
    NecessaryConcreteAt noTotalityCause false ∧
    ¬ PossiblyExternallyCausedAt noTotalityCause false := by
  constructor
  · exact ⟨none, True.intro, True.intro, fun _ _ => True.intro⟩
  · intro h
    rcases h with ⟨v, _, _, c, _, _, hc, _⟩
    exact hc

end TruthCore.Causality.PossibleCauseOfContingency
