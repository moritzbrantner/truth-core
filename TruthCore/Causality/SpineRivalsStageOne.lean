module

public import TruthCore.Causality.InertEmptiness
public import TruthCore.Causality.LocalFramePossibleExternalCause

/-!
# Rivals of the stage-one premises of the modal spine

Analyst formulations for `docs/notes/modal-spine.md`; attribution deferred. Each
definition is a positive rival position to one stage-one premise, typed on that
premise's carrier. None is asserted. The controls show each rival jointly
satisfiable with the other premises of the consuming theorem while that
theorem's conclusion fails. A finite interpretation is evidence only about the
encoded vocabulary.

* `ActualIrreflexiveSerial`: accessibility read as "what lies ahead" or "what
  would be ideal" rather than alethic possibility: every world sees some world,
  the selected world does not see itself. Rival of actual reflexivity.
* `ReflexiveNonEuclidean`: every world is possible relative to itself, but two
  possibilities of one world need not be possible relative to each other.
  Motivated by arguments that metaphysical possibility is not transitive
  (small-change series about a thing's origin). Rival of the Euclidean premise.
* `PresentistGap`: existence in a history is presence at its designated now, and
  something was present at another time that is not present now. Motivated by
  presentism about existence. Rival of presence-to-existence.
* `EternalContingencyAt`: contingent concrete things exist and no accessible
  history is one in which contingent concrete reality begins. Motivated by
  steady-state and eternal-world views. Rival of the possible beginning.
* `BruteBeginningsOnlyAt`: a beginning of contingent concrete reality is
  possible, and no possible beginning has an existing concrete external cause.
  Motivated by brute-beginning views. Rival of the causal opportunity.
-/

@[expose] public section

namespace TruthCore.Causality.SpineRivalsStageOne

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.PossibleCauseOfContingency

/-- Every world accesses some world, and the selected world does not access
itself. Incompatible with `ActualReflexive` at that world; stronger than its
negation by the seriality conjunct. -/
def ActualIrreflexiveSerial {W B : Type} (m : Ontic W B) (w : W) : Prop :=
  ¬ m.frame.access w w ∧ ∀ v, ∃ u, m.frame.access v u

/-- Every world accesses itself, and some world accesses two worlds of which the
first does not access the second. Incompatible with `Euclidean`; stronger than
its negation by the reflexivity conjunct. -/
def ReflexiveNonEuclidean {W : Type} (frame : TruthCore.Modal.Frame W) : Prop :=
  (∀ w, frame.access w w) ∧
    ∃ w a b, frame.access w a ∧ frame.access w b ∧ ¬ frame.access a b

/-- World-relative existence is exactly presence at the designated now, and some
individual is present at a time of a history without being present at its now.
Incompatible with `HistoryPresenceActual`; stronger than its negation. -/
def PresentistGap {W B T : Type} (h : History W B T) : Prop :=
  CoherentAtNow h ∧ ∃ v x t, h.IsAt v x t ∧ ¬ h.IsAt v x h.now

/-- Some concrete individual is contingent at `w`, and no history accessible
from `w` satisfies the supplied beginning predicate. Incompatible with
`PossiblyBeginsAt`; stronger than its negation by the first conjunct. -/
def EternalContingencyAt {W B : Type} (s : Scenario W B) (w : W) : Prop :=
  (∃ x, s.concrete x ∧ ContingentAt s.ontic w x) ∧
    ∀ v, s.ontic.frame.access w v → ¬ s.beginsContingency v

/-- A beginning is possible and no accessible beginning has an existing concrete
external cause. Classically the exact negation of `CausalOpportunityAt`. -/
def BruteBeginningsOnlyAt {W B : Type} (s : Scenario W B) (w : W) : Prop :=
  PossiblyBeginsAt s w ∧ ¬ PossiblyExternallyCausedAt s w

namespace Control

open TruthCore.Causality.InertEmptiness
open TruthCore.Causality.InertEmptiness.Control (all)

/-- Three worlds: the selected one and two others. -/
inductive Place where
  | actual | near | far
  deriving DecidableEq

/-- Seen from everywhere: `near` and `far`, never `actual`. -/
def ahead : TruthCore.Modal.Frame Place := ⟨fun _ b => b ≠ Place.actual⟩

/-- Every world sees itself; `actual` also sees `near`, and `near` sees `far`. -/
def stepwise : TruthCore.Modal.Frame Place :=
  ⟨fun a b => a = b ∨ (a = Place.actual ∧ b = Place.near) ∨ (a = Place.near ∧ b = Place.far)⟩

/-- Individual `false` exists at `near` and `far`; individual `true` exists at
`near` only. Nothing exists at `actual`. -/
def existsAway : Place → Bool → Prop :=
  fun w x => (x = false ∧ w ≠ Place.actual) ∨ (x = true ∧ w = Place.near)

/-- `false` is present at every time where it exists; `true` is present at
`near` at time 1 only. -/
def presentAway : Place → Bool → Nat → Prop :=
  fun w x t => (x = false ∧ w ≠ Place.actual) ∨ (x = true ∧ w = Place.near ∧ t = 1)

/-- The three-world history over the forward-looking frame. -/
def aheadHistory : History Place Bool Nat where
  ontic := { frame := ahead, ExistsAt := existsAway, Causes := fun _ _ _ => False }
  IsAt := presentAway
  now := 1

/-- The same history over the reflexive, non-Euclidean frame. -/
def stepwiseHistory : History Place Bool Nat where
  ontic := { frame := stepwise, ExistsAt := existsAway, Causes := fun _ _ _ => False }
  IsAt := presentAway
  now := 1

/-- Presentist history on two mutually accessible worlds: at world `true`
individual `false` is present at time 0 only and individual `true` from time 1
on; existence is presence at now = 1. -/
def presentist : History Bool Bool Nat where
  ontic := { frame := ⟨fun _ _ => True⟩,
             ExistsAt := fun w x => w = true ∧ x = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => w = true ∧ ((x = false ∧ t = 0) ∨ (x = true ∧ t ≠ 0))
  now := 1

/-- Two mutually accessible worlds, each with its own contingent individual, and
no history in which contingent reality begins. -/
def eternal : Scenario Bool Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w x => w = x,
             Causes := fun _ _ _ => False }
  concrete := fun _ => True
  beginsContingency := fun _ => False
  causesContingencyTotality := fun _ _ => False

/-- Each rival with the other premises of its consuming theorem and that
theorem's conclusion failing. Groups 1 to 3 concern
`InertEmptiness.necessaryConcrete`; groups 4 and 5 concern
`LocalFramePossibleExternalCause.necessaryConcrete`. -/
def Certificate : Prop :=
  (ActualIrreflexiveSerial aheadHistory.ontic Place.actual ∧
    TruthCore.Modal.Euclidean ahead ∧
    CountTemporalNecessity.HistoryPresenceActual aheadHistory ∧
    EmptinessStaysEmpty aheadHistory all ∧
    PossiblyContingentsAbsentThenPresent aheadHistory all Place.actual ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨aheadHistory.ontic, all, fun _ _ _ => False⟩ Place.actual) ∧
  (ReflexiveNonEuclidean stepwise ∧
    NecessarilyUnderived.ActualReflexive stepwiseHistory.ontic Place.actual ∧
    CountTemporalNecessity.HistoryPresenceActual stepwiseHistory ∧
    EmptinessStaysEmpty stepwiseHistory all ∧
    PossiblyContingentsAbsentThenPresent stepwiseHistory all Place.actual ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨stepwiseHistory.ontic, all, fun _ _ _ => False⟩ Place.actual) ∧
  (PresentistGap presentist ∧
    TruthCore.Modal.Euclidean presentist.ontic.frame ∧
    NecessarilyUnderived.ActualReflexive presentist.ontic true ∧
    EmptinessStaysEmpty presentist all ∧
    PossiblyContingentsAbsentThenPresent presentist all true ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨presentist.ontic, all, fun _ _ _ => False⟩ true) ∧
  (EternalContingencyAt eternal false ∧
    TruthCore.Modal.Euclidean eternal.ontic.frame ∧
    NecessarilyUnderived.ActualReflexive eternal.ontic false ∧
    CausalOpportunityAt eternal false ∧
    ¬ PossibleCauseOfContingency.NecessaryConcreteAt eternal false) ∧
  (BruteBeginningsOnlyAt bruteOnly false ∧
    TruthCore.Modal.Euclidean bruteOnly.ontic.frame ∧
    NecessarilyUnderived.ActualReflexive bruteOnly.ontic false ∧
    ¬ PossibleCauseOfContingency.NecessaryConcreteAt bruteOnly false)

end Control

end TruthCore.Causality.SpineRivalsStageOne
