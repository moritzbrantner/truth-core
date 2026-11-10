module

public import TruthCore.Causality.InertEmptiness
public import Mathlib.Data.Int.Order.Basic

/-!
# Contingent things that come to be, in a history with a founded past

Analyst formulation for the modal spine to "God exists"
(`docs/notes/modal-spine.md`, premise A3). Attribution deferred.

Ordinary meaning. A contingent concrete thing *comes to be* in a history when,
whenever it is present, there was an earlier moment at which it was absent.
A moment has a *founded past* when there is no endless descending sequence of
moments below it. The possibility premise defined here says: some possible
history has a founded-past moment at which a contingent concrete thing is
present, and in that history every contingent concrete thing comes to be.

Examples. A history with a first moment at which only a necessary thing is
present, and a contingent thing appearing later, satisfies it. A history whose
contingent things are present at its first moment does not: they never came to
be. A history with an endless past in which each contingent thing is preceded
by another does not: no moment has a founded past.

Distinctions. Coming to be is not being caused, and not having a first moment
of presence (a dense order may have none). A founded past is not a finite past
and is weaker than a first moment of time for the whole order: it concerns the
moments below one moment only. The premise is a possibility claim about one
accessible history and says nothing about the actual world.

Relation to the Third Way. The corpus records that "each thing is at some time
not" does not entail "at some time nothing is"
(`TruthCore.Logic.EachSometimeNotDoesNotEntailSometimeNothing`). Here the
premise is "absent at some *earlier* moment" together with a founded past, and
the conclusion is restricted to contingent concrete things; under those two
changes the step is valid. Nothing is attributed to Aquinas.

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.ContingentComingToBe

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.InertEmptiness

/-- In history `v`, every contingent concrete individual, at every moment at
which it is present, has a strictly earlier moment at which it is absent.
Nothing is said about non-contingent or non-concrete individuals. -/
def AllContingentsComeToBeAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W) : Prop :=
  ∀ x, Concrete x → ContingentAt h.ontic v x →
    ∀ t, h.IsAt v x t → ∃ s, s < t ∧ ¬ h.IsAt v x s

/-- History `v` has a moment with a founded past (`Acc` of the strict order:
no endless descent below it) at which some contingent concrete individual is
present, and every contingent concrete individual of `v` comes to be. -/
def FoundedComingToBeAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W) : Prop :=
  AllContingentsComeToBeAt h Concrete v ∧
    ∃ x t, Concrete x ∧ ContingentAt h.ontic v x ∧ h.IsAt v x t ∧
      Acc (fun a b : T => a < b) t

/-- Some history accessible from `w` is one of founded coming-to-be. -/
def PossiblyFoundedComingToBe {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ FoundedComingToBeAt h Concrete v

namespace Control

open TruthCore.Causality.InertEmptiness.Control (universal all initialState rooted)

/-- Endless generation: worlds are booleans, individuals and times are integers.
Individual `n` exists only at world `true` and is present there from time `n`
on. Every individual comes to be, some individual is present at every time, and
no time has a founded past. -/
def endless : History Bool Int Int where
  ontic := { frame := universal, ExistsAt := fun w _ => w = true, Causes := fun _ _ _ => False }
  IsAt := fun w x t => w = true ∧ x ≤ t
  now := 0

/-- Where the rival of the possible contingent-free past survives, and where the
new premise holds. (1) Endless generation: presence-to-existence, inert
emptiness and universal coming-to-be hold, no accessible history has a
contingent-free moment before a populated one, no time has a founded past, and
no individual exists at both worlds. (2) The existing initial-state control: its
time 0 has a founded past, but its contingent individual does not come to be.
(3) The existing rooted control satisfies the new premise. -/
def Certificate : Prop :=
  (CountTemporalNecessity.HistoryPresenceActual endless ∧
    EmptinessStaysEmpty endless all ∧
    AllContingentsComeToBeAt endless all true ∧
    NoPossibleContingentFreePast endless all true ∧
    (∀ t : Int, ¬ Acc (fun a b : Int => a < b) t) ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨endless.ontic, all, fun _ _ _ => False⟩ true) ∧
  (Acc (fun a b : Nat => a < b) 0 ∧
    ¬ AllContingentsComeToBeAt initialState all true) ∧
  PossiblyFoundedComingToBe rooted all true

end Control

end TruthCore.Causality.ContingentComingToBe
