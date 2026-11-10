module

public import TruthCore.Causality.CountTemporalNecessity
public import TruthCore.Causality.BruteFoundationBoundary
public import TruthCore.Causality.NecessarilyUnderived
public import TruthCore.Modal.Kripke
public import Mathlib.Order.Nat

/-!
# Inert emptiness: nothing concrete comes after nothing concrete

Analyst formulation for the modal spine to "God exists" (stage one: a
necessary concrete being exists). Attribution deferred; no source is claimed.

Ordinary meaning. A moment of a history is *concrete-empty* when no concrete
thing is present at it. *Inert emptiness* says such a moment is never followed,
in the same history, by a moment at which something concrete is present:
"from nothing, nothing comes", read temporally and only for concrete things.

Examples. A history in which a stone is present at every moment satisfies it
trivially. A history with one empty moment followed by a populated one (a
beginning out of nothing) violates it. A history whose contingent things are
present from its earliest moment, with no moment before them, satisfies it:
the principle is silent about a first state that has no earlier moment.

Distinctions. It is not a causal principle: no cause, ground or explanation
relation occurs. It is not the principle of sufficient reason, and it does not
say that every beginning has a cause. It does not say that times are linearly
ordered, that there is a first or last moment, or that anything persists.
It is not modal: each instance concerns two moments of one history.

Reuse. Worlds, beings, times and presence are the existing
`TruthCore.Modal.TemporalHistory.History`; the presence-to-existence contract
is the existing `CountTemporalNecessity.HistoryPresenceActual`; the conclusion
is the existing `BruteFoundationBoundary.NecessaryConcreteAt`. The `beginsContingency`
and `causesContingencyTotality` primitives of `PossibleCauseOfContingency.Scenario`
are deliberately not used: this route needs neither.

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.InertEmptiness

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory

/-- No concrete individual is present at time `t` of history `v`. Abstract
individuals, and concrete ones present at other times, are not excluded. -/
def ConcreteEmptyAt {W B T : Type} (h : History W B T) (Concrete : B → Prop)
    (v : W) (t : T) : Prop :=
  ∀ x, Concrete x → ¬ h.IsAt v x t

/-- In every history, a concrete-empty moment is followed only by
concrete-empty moments. Stated for every strictly later moment of the supplied
preorder, not only an immediate successor; incomparable moments are unconstrained. -/
def EmptinessStaysEmpty {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) : Prop :=
  ∀ v s t, s < t → ConcreteEmptyAt h Concrete v s → ConcreteEmptyAt h Concrete v t

/-- The rival: some history has a concrete-empty moment strictly before a
moment at which something concrete is present. -/
def EmptinessBecomesPopulated {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) : Prop :=
  ∃ v s t, s < t ∧ ConcreteEmptyAt h Concrete v s ∧ ∃ x, Concrete x ∧ h.IsAt v x t

/-- In history `v` there is a moment at which no contingent concrete individual
is present, strictly before a moment at which one is. Contingency is the
existing modal `ContingentAt`: existing at `v` and absent from some accessible
world. No first moment of contingent reality, cause or totality is asserted,
and nothing is said about whether anything else is present at the earlier moment. -/
def ContingentsAbsentThenPresentAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W) : Prop :=
  ∃ s t, s < t ∧
    (∀ x, Concrete x → ContingentAt h.ontic v x → ¬ h.IsAt v x s) ∧
    ∃ x, Concrete x ∧ ContingentAt h.ontic v x ∧ h.IsAt v x t

/-- Some history accessible from `w` has a moment free of contingent concrete
individuals before a moment containing one. A possibility claim: it need not
hold of `w` itself. -/
def PossiblyContingentsAbsentThenPresent {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ ContingentsAbsentThenPresentAt h Concrete v

/-- The rival: in no history accessible from `w` is a moment free of contingent
concrete individuals followed by one containing some. An "initial state" view on
which contingent things are present from the earliest moment of every possible
history satisfies it; so does a view with no contingent concrete things at all. -/
def NoPossibleContingentFreePast {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ¬ ContingentsAbsentThenPresentAt h Concrete v

namespace Control

/-- Two worlds, each accessible from each. -/
def universal : TruthCore.Modal.Frame Bool := ⟨fun _ _ => True⟩

/-- Out of nothing: one individual, existing only at world `true`, present
there only at the later time. The earlier moment of world `true` is empty. -/
def exNihilo : History Bool Unit Nat where
  ontic := { frame := universal, ExistsAt := fun w _ => w = true, Causes := fun _ _ _ => False }
  IsAt := fun w _ t => w = true ∧ t = 1
  now := 1

/-- Initial state: one individual, existing only at world `true`, present there
at every time. No moment precedes contingent reality. -/
def initialState : History Bool Unit Nat where
  ontic := { frame := universal, ExistsAt := fun w _ => w = true, Causes := fun _ _ _ => False }
  IsAt := fun w _ _ => w = true
  now := 1

/-- Presence without existence: individual `false` is present at every time of
every world but exists at none; individual `true` exists only at world `true`
and is present there only at the later time. -/
def phantom : History Bool Bool Nat where
  ontic := { frame := universal, ExistsAt := fun w x => x = true ∧ w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => x = false ∨ (w = true ∧ t = 1)
  now := 1

/-- Joint witness: individual `false` exists at both worlds and is present at
every time; individual `true` exists only at world `true` and is present there
only at the later time. -/
def rooted : History Bool Bool Nat where
  ontic := { frame := universal, ExistsAt := fun w x => x = false ∨ w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => x = false ∨ (w = true ∧ t = 1)
  now := 1

/-- Every individual counts as concrete in the controls: they test temporal and
modal structure, not the concrete/abstract line. -/
def all {B : Type} : B → Prop := fun _ => True

/-- The frame conditions and one premise bundle minus one member, in each of
three interpretations where the conclusion fails; and the full bundle with a
populated conclusion in a fourth. The grounding field is empty in every
control: the conclusion does not mention it. -/
def Certificate : Prop :=
  (TruthCore.Modal.Euclidean universal ∧ universal.access true true) ∧
  -- omit inert emptiness
  (CountTemporalNecessity.HistoryPresenceActual exNihilo ∧
    PossiblyContingentsAbsentThenPresent exNihilo all true ∧
    EmptinessBecomesPopulated exNihilo all ∧
    ¬ EmptinessStaysEmpty exNihilo all ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨exNihilo.ontic, all, fun _ _ _ => False⟩ true) ∧
  -- omit the possible contingent-free past
  (CountTemporalNecessity.HistoryPresenceActual initialState ∧
    EmptinessStaysEmpty initialState all ∧
    NoPossibleContingentFreePast initialState all true ∧
    (∃ x, ContingentAt initialState.ontic true x) ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨initialState.ontic, all, fun _ _ _ => False⟩ true) ∧
  -- omit presence-to-existence
  (¬ CountTemporalNecessity.HistoryPresenceActual phantom ∧
    EmptinessStaysEmpty phantom all ∧
    PossiblyContingentsAbsentThenPresent phantom all true ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨phantom.ontic, all, fun _ _ _ => False⟩ true) ∧
  -- joint witness of the full bundle
  (CountTemporalNecessity.HistoryPresenceActual rooted ∧
    EmptinessStaysEmpty rooted all ∧
    PossiblyContingentsAbsentThenPresent rooted all true ∧
    ContingentAt rooted.ontic true true ∧
    BruteFoundationBoundary.NecessaryConcreteAt
        ⟨rooted.ontic, all, fun _ _ _ => False⟩ true)

end Control

end TruthCore.Causality.InertEmptiness
