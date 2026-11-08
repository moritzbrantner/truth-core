module

public import TruthCore.Causality.PureActThisness

/-! Follow-up to the pure-act thisness fork (#320): a narrower bridge against
bare numerical difference. Analyst formulation, attribution deferred.

Identity of real indiscernibles (`RealDeterminationsIndividuate`) denies bare
difference everywhere, including Black-style spheres. The narrower bridge
denies it only among beings ALL of whose real determinations are pure: bare
distinctness needs some non-pure principle of multiplicity (a place, matter,
a subject, a receiving principle) in at least one of the two beings. -/

@[expose] public section

namespace TruthCore.Causality.PureIndiscernibility
open TruthCore.Case.Catholicism
open TruthCore.Causality.PureActThisness

variable {B R D : Type}

/-- Two beings with the same real determinations, all of them pure, are one.
Contrapositively (classically): distinct really indiscernible beings include
one with a non-pure determination. Vacuous at every being that has a non-pure
determination; it also applies to beings with no real determinations at all. -/
def PurelyDeterminedIndiscerniblesIdentical (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ x y, (∀ d, Has x d → Pure d) → (∀ d, Has x d ↔ Has y d) → x = y

/-- Only first movers are purely determined: every being whose real
determinations are all pure is a first mover. The background under which the
narrower bridge says no more than uniqueness. -/
def OnlyFirstMoversPurelyDetermined
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ x, (∀ d, Has x d → Pure d) → IsFirstUnmovedMover Moved Moves x

namespace Control
open TruthCore.Causality.PureActThisness.Control
open TruthCore.Causality.PartFreePlurality

/-- Black-style carrier on the single-mover table: `true` is a pure perfection
that only `g` has; `false` is a shared non-pure determination ("located") that
every other being has. The non-first movers are really indiscernible. -/
def sphereHas (a : JB) (d : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop) (¬ a = .g) (a = .g) d

def spherePure (d : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop) False True d

/-- Finite interpretations and one general equivalence; satisfiability of the
encoded bundles, not metaphysical possibility.
* Black-style: unrestricted perfection, strict pure actuality, the narrower
  bridge and at-most-one hold with an actual first mover while identity of real
  indiscernibles fails.
* Reach: with determination-free inert rows, the two pure-act premises and
  at-most-one hold while the narrower bridge fails, so it exceeds uniqueness only
  through purely determined beings that are not first movers.
* Equivalence: if only first movers are purely determined, then under the two
  pure-act premises the narrower bridge is equivalent to at-most-one.
* Omissions: each of the three premises of `uniqueFromPureIndiscernibility` is
  omitted in turn with the other two retained and at-most-one failing. -/
def Certificate : Prop :=
  (FirstMoverHasEveryPureDetermination jMoved jMoves sphereHas spherePure ∧
    FirstMoverDeterminationsArePure jMoved jMoves sphereHas spherePure ∧
    PurelyDeterminedIndiscerniblesIdentical sphereHas spherePure ∧
    AtMostOneFirstUnmovedMover jMoved jMoves ∧
    IsFirstUnmovedMover jMoved jMoves (.g : JB) ∧
    ¬ RealDeterminationsIndividuate sphereHas) ∧
  (FirstMoverHasEveryPureDetermination jMoved jMoves onlyGHas (fun _ => True) ∧
    FirstMoverDeterminationsArePure jMoved jMoves onlyGHas (fun _ => True) ∧
    AtMostOneFirstUnmovedMover jMoved jMoves ∧
    ¬ PurelyDeterminedIndiscerniblesIdentical onlyGHas (fun _ => True)) ∧
  (∀ {B R D : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
      (Has : B → D → Prop) (Pure : D → Prop),
    FirstMoverHasEveryPureDetermination Moved Moves Has Pure →
    FirstMoverDeterminationsArePure Moved Moves Has Pure →
    OnlyFirstMoversPurelyDetermined Moved Moves Has Pure →
    (PurelyDeterminedIndiscerniblesIdentical Has Pure ↔ AtMostOneFirstUnmovedMover Moved Moves)) ∧
  -- bridge omitted: the unchanged part-free model
  (FirstMoverHasEveryPureDetermination moved moves actHas allPure ∧
    FirstMoverDeterminationsArePure moved moves actHas allPure ∧
    ¬ PurelyDeterminedIndiscerniblesIdentical actHas allPure ∧
    ¬ AtMostOneFirstUnmovedMover moved moves) ∧
  -- strict pure actuality omitted
  (FirstMoverHasEveryPureDetermination moved moves thisHas actOnly ∧
    ¬ FirstMoverDeterminationsArePure moved moves thisHas actOnly ∧
    PurelyDeterminedIndiscerniblesIdentical thisHas actOnly ∧
    ¬ AtMostOneFirstUnmovedMover moved moves) ∧
  -- unrestricted perfection omitted
  (¬ FirstMoverHasEveryPureDetermination moved moves thisHas everyPure ∧
    FirstMoverDeterminationsArePure moved moves thisHas everyPure ∧
    PurelyDeterminedIndiscerniblesIdentical thisHas everyPure ∧
    ¬ AtMostOneFirstUnmovedMover moved moves)

end Control
end TruthCore.Causality.PureIndiscernibility
