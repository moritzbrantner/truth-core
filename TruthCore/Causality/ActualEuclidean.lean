module

public import TruthCore.Causality.SpineRivalsStageOne

/-!
# Euclidean access at the actual world only

Analyst formulation for the modal spine to "God exists" (stage one); attribution
deferred. Both stage-one arrivals (`InertEmptiness.necessaryConcrete` and
`LocalFramePossibleExternalCause.necessaryConcrete`) use their global Euclidean
premise only at the selected world `w`: the instances are `hEuclidean w v w` and
`hEuclidean w v z`. This module states that restricted condition.

Ordinary meaning. Read worlds as complete histories and access as metaphysical
possibility. `EuclideanAt frame w` says: any two histories possible relative to
the actual history `w` are possible relative to each other. It says nothing
about what is possible relative to a merely possible history beyond the other
possibilities of `w`.

Examples. Every Euclidean (in particular every S5) frame satisfies it at every
world. The frame `Control.clustered` below satisfies it at `actual` but not
globally: `near` sees `far`, which `actual` does not see, and `far` does not see
`near` back. The existing `SpineRivalsStageOne.Control.stepwise` frame fails it
at `actual`: `actual` sees `near`, `near` does not see `actual`.

Distinctions. It is weaker than global Euclideanness, not transitivity, and not
symmetry; with reflexivity at `w` it gives, for each successor `v` of `w`, that
`v` sees `w` back and sees every successor of `w`.

Applicability of the definition to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.ActualEuclidean

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SpineRivalsStageOne.Control (Place)

/-- Any two worlds accessible from `w` access one another. Global
`TruthCore.Modal.Euclidean` is this condition at every world. -/
def EuclideanAt {W : Type} (frame : TruthCore.Modal.Frame W) (w : W) : Prop :=
  ∀ v z, frame.access w v → frame.access w z → frame.access v z

/-- Transport an individual necessary at an accessible world to the selected
world, using Euclidean access and reflexivity at that world only. Same
algorithm as `NonlimitingConcreteExistence.necessaryAtOrigin`. -/
theorem necessaryAtOrigin {W B : Type} (m : Ontic W B) (w v : W) (c : B)
    (hEuclidean : EuclideanAt m.frame w)
    (hReflexive : TruthCore.Causality.NecessarilyUnderived.ActualReflexive m w)
    (hwv : m.frame.access w v) (hn : NecessaryAt m v c) :
    m.ExistsAt w c ∧ NecessaryAt m w c :=
  ⟨hn w (hEuclidean v w hwv hReflexive), fun z hwz => hn z (hEuclidean v z hwv hwz)⟩

namespace Control

/-- `actual` and `near` see each other and themselves; `near` also sees `far`;
`far` sees only itself. -/
def clustered : TruthCore.Modal.Frame Place :=
  ⟨fun a b => a = b ∨ (a = Place.actual ∧ b = Place.near) ∨
    (a = Place.near ∧ b = Place.actual) ∨ (a = Place.near ∧ b = Place.far)⟩

/-- Individual `false` exists at every world and is present at every time;
individual `true` exists at `near` only and is present there at time 1 only. -/
def clusteredHistory : History Place Bool Nat where
  ontic := { frame := clustered,
             ExistsAt := fun w x => x = false ∨ (x = true ∧ w = Place.near),
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => x = false ∨ (x = true ∧ w = Place.near ∧ t = 1)
  now := 1

/-- The separating model and the status of the existing stepwise control.
(1) `clustered` is Euclidean and reflexive at `actual` but not Euclidean.
(2) On it, presence-to-existence, inert emptiness and the possible
contingent-free past hold at `actual`, so the restricted bundle of the inert
emptiness arrival is jointly satisfiable while global Euclideanness fails.
(3) The existing reflexive non-Euclidean `stepwise` frame is not Euclidean at
`actual`, so it is also a countermodel to the restricted premise's omission. -/
def Certificate : Prop :=
  (EuclideanAt clustered Place.actual ∧ clustered.access Place.actual Place.actual ∧
    ¬ TruthCore.Modal.Euclidean clustered) ∧
  (CountTemporalNecessity.HistoryPresenceActual clusteredHistory ∧
    TruthCore.Causality.InertEmptiness.EmptinessStaysEmpty clusteredHistory
      TruthCore.Causality.InertEmptiness.Control.all ∧
    TruthCore.Causality.InertEmptiness.PossiblyContingentsAbsentThenPresent
      clusteredHistory TruthCore.Causality.InertEmptiness.Control.all Place.actual) ∧
  ¬ EuclideanAt TruthCore.Causality.SpineRivalsStageOne.Control.stepwise Place.actual

end Control

end TruthCore.Causality.ActualEuclidean
