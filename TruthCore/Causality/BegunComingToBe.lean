module

public import TruthCore.Causality.ContingentComingToBe
public import TruthCore.Causality.BruteFoundationBoundary
public import TruthCore.Causality.CountTemporalNecessity
public import Mathlib.Order.WithBot

/-!
# Coming to be in a history whose past has a beginning

Analyst formulation for the modal spine to "God exists"
(`docs/notes/modal-spine.md`, premise A3′). Attribution deferred.

`ContingentComingToBe.PossiblyFoundedComingToBe` asks for a populated moment
with a *founded* past: `Acc` of the strict order, no endless descending sequence
of moments below it. Its proof of premise A3 uses foundedness only to obtain a
moment with nothing earlier. This module asks for exactly that.

Ordinary meaning. The past of a moment `t` *has a beginning* when some moment at
or before `t` has no moment before it: a first moment. A history of *begun
coming-to-be* has a moment with a begun past at which a contingent concrete
thing is present, and in it every contingent concrete thing comes to be (was
absent at some earlier moment whenever it is present).

Examples. Discrete time with a first moment, and continuous time with a first
moment (the standard picture of a universe with a beginning), both give every
moment a begun past. Continuous time with a first moment does not give a founded
past: below any later moment `t` lies the endless descent `t, t/2, t/4, …`.
An endless discrete past and an open-below continuous past (no first moment)
have no begun moment.

Distinctions. A begun past is not a finite past: infinitely many moments may lie
between the beginning and `t`. It is weaker than a founded past
(`begunOfAcc`); the control `Control.zeno` shows the weakening is strict. The
beginning is a first moment of the supplied order, not a first event, cause or
state, and nothing here says what, if anything, is present at it. The premise
is a possibility claim about one accessible history.

With the weaker premise the rival's second horn is a genuinely *beginningless*
past (no first moment at or below some populated moment), not merely a
non-well-founded one, and premise A3′ no longer carries a price against
continuous time.

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.BegunComingToBe

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.InertEmptiness
open TruthCore.Causality.ContingentComingToBe

/-- The past of `t` has a beginning: some moment at or before `t` has no
strictly earlier moment. -/
def BegunAt {T : Type} [Preorder T] (t : T) : Prop :=
  ∃ m, (m = t ∨ m < t) ∧ ∀ r, ¬ r < m

/-- History `v` has a moment with a begun past at which some contingent concrete
individual is present, and every contingent concrete individual of `v` comes to
be. As `FoundedComingToBeAt`, with `BegunAt` in place of `Acc`. -/
def BegunComingToBeAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W) : Prop :=
  AllContingentsComeToBeAt h Concrete v ∧
    ∃ x t, Concrete x ∧ ContingentAt h.ontic v x ∧ h.IsAt v x t ∧ BegunAt t

/-- Some history accessible from `w` is one of begun coming-to-be. -/
def PossiblyBegunComingToBe {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ BegunComingToBeAt h Concrete v

namespace Control

open TruthCore.Causality.InertEmptiness.Control (universal all)

/-- A history with a first moment `⊥` and no earliest moment after it.
Worlds are booleans, individuals integers, times `WithBot ℤ`. At world `true`
individual `n` exists and is present at every integer time `t ≥ n`; nothing is
present at `⊥`. At world `false` nothing exists. Every individual is contingent,
comes to be, and is preceded at every moment of its presence by individual
`n - 1`, present one moment earlier. The integers below any time give an endless
descent, as `t, t/2, t/4, …` do in continuous time with a beginning. -/
def zeno : History Bool Int (WithBot Int) where
  ontic := { frame := universal, ExistsAt := fun w _ => w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w n t => w = true ∧ (n : WithBot Int) ≤ t
  now := ((0 : Int) : WithBot Int)

/-- Each individual is grounded by its predecessor, at world `true`. -/
def predecessorGrounds : Bool → Int → Int → Prop := fun w y x => w = true ∧ y = x - 1

/-- The dense-with-beginning control, every individual counted concrete:
begun coming-to-be is possible; founded coming-to-be is not; presence gives
existence; every contingent concrete individual has a concrete ground present
at a strictly earlier moment whenever it is present; no concrete individual is
necessary at `true`; and emptiness does not stay empty (inert emptiness, premise
A2, fails). So begun coming-to-be together with earlier-present grounds of
every contingent thing does not by itself require a necessary concrete
individual: in this arrival necessity enters through inert emptiness. -/
def Certificate : Prop :=
  PossiblyBegunComingToBe zeno all true ∧
  ¬ PossiblyFoundedComingToBe zeno all true ∧
  CountTemporalNecessity.HistoryPresenceActual zeno ∧
  (∀ x t, ContingentAt zeno.ontic true x → zeno.IsAt true x t →
    ∃ y s, zeno.ontic.ExistsAt true y ∧ predecessorGrounds true y x ∧
      s < t ∧ zeno.IsAt true y s) ∧
  ¬ BruteFoundationBoundary.NecessaryConcreteAt ⟨zeno.ontic, all, predecessorGrounds⟩ true ∧
  ¬ EmptinessStaysEmpty zeno all

end Control

end TruthCore.Causality.BegunComingToBe
