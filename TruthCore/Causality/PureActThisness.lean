module

public import TruthCore.Causality.RootMultiplication

/-! Can primitive thisness distinguish two unrestricted pure acts? (#320)

Analyst formulation, attribution deferred: nothing here is attributed to
Aquinas, Scotus, Leibniz or Adams, is a definition of God, or settles whether
the represented relations are real.

The earlier #697 fork (`RootMultiplication`) works with a represented `essence`
map, so a primitive thisness appears there only as an unexplained difference of
map values. Here the candidate's constitution is typed instead: `Has x d` says
that `d` is a *real determination* of `x` (an intrinsic constituent or a real
relation, not a mere description such as "is identical with x"), and `Pure d`
says that `d` is a *pure perfection*: an actuality that involves no potency,
limitation or reception. Determinations that are not pure are limits, receiving
or individuating principles, potencies or privations.

Four proposed bases for two distinct first movers map onto one fork:
* a different perfection is a pure determination one has and the other lacks;
* a different essence, differentia or receiving principle is a non-pure real
  determination;
* a real relational role is a real determination of one of these two kinds,
  while a merely extrinsic role is no real determination at all;
* a primitive thisness is either a real determination (`FirstMoverHasRealThisness`)
  or no determination: bare numerical difference of really indiscernible beings.

Unrestricted perfection removes the first kind, strict pure actuality the
second; together they leave only bare difference (`FirstMoversReallyIndiscernible`).
Real thisness is then itself a pure perfection, which every first mover has, so
it cannot distinguish them. Bare difference is excluded only by a principle that
real determinations individuate, which ranges over all beings. -/

@[expose] public section

namespace TruthCore.Causality.PureActThisness
open TruthCore.Case.Catholicism

variable {B R D : Type}

/-- Unrestricted perfection over real determinations: every first mover really
has every pure perfection. Ordinary immaterial simplicity (a form free of matter
that still lacks other forms' perfections) does not satisfy this. -/
def FirstMoverHasEveryPureDetermination
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover Moved Moves f → ∀ d, Pure d → Has f d

/-- Strict pure actuality: each real determination of a first mover is a pure
perfection. A first mover has no real limiting, receiving or individuating
principle that is not itself an actuality without potency. This is stronger than
absence of matter, of parts or of esse other than essence. -/
def FirstMoverDeterminationsArePure
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover Moved Moves f → ∀ d, Has f d → Pure d

/-- Any two first movers have exactly the same real determinations. This is not
numerical identity: two beings can be really indiscernible and still distinct. -/
def FirstMoversReallyIndiscernible
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (Has : B → D → Prop) : Prop :=
  ∀ f g, IsFirstUnmovedMover Moved Moves f → IsFirstUnmovedMover Moved Moves g →
    ∀ d, Has f d ↔ Has g d

/-- Real thisness: each first mover has a real determination that no other being
has. The thisness is an intrinsic real determination; a merely logical predicate
"identical with f" is not a value of `Has` unless the interpretation makes it one. -/
def FirstMoverHasRealThisness
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (Has : B → D → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover Moved Moves f → ∃ d, Has f d ∧ ∀ y, Has y d → y = f

/-- Identity of real indiscernibles, over ALL beings of the carrier: beings with the
same real determinations are one. It is stronger than its first-mover instance and
denies bare numerical difference anywhere (for example, two qualitatively
identical spheres). -/
def RealDeterminationsIndividuate (Has : B → D → Prop) : Prop :=
  ∀ x y, (∀ d, Has x d ↔ Has y d) → x = y

/-- The bare-identity rival: two distinct first movers with the same real
determinations. Their numerical difference is primitive, not grounded in any
real determination. -/
def BarelyDistinctFirstMovers
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (Has : B → D → Prop) : Prop :=
  ∃ f g, IsFirstUnmovedMover Moved Moves f ∧ IsFirstUnmovedMover Moved Moves g ∧
    f ≠ g ∧ ∀ d, Has f d ↔ Has g d

namespace Control
open TruthCore.Causality.PartFreePlurality

abbrev JB := TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.B
abbrev JR := TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.R
abbrev jMoved := TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.movedIn
abbrev jMoves := TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.movesIn

/-- The unchanged part-free model, read so that each act respect is a real
determination and every respect is a pure perfection. -/
def actHas : Being → Respect → Prop := inAct
def allPure : Respect → Prop := fun _ => True

/-- Part-free roots that also carry a real individuating determination each.
`Sum.inr b` is the thisness of `b`; the original act respects are unchanged. -/
def thisHas (x : Being) : Respect ⊕ Being → Prop :=
  Sum.rec (motive := fun _ => Prop) (fun r => inAct x r) (fun b => x = b)

/-- The thisnesses are not pure perfections: individuating principles. -/
def actOnly : Respect ⊕ Being → Prop :=
  Sum.rec (motive := fun _ => Prop) (fun _ => True) (fun _ => False)

/-- Every determination, the thisnesses included, counts as a pure perfection. -/
def everyPure : Respect ⊕ Being → Prop := fun _ => True

/-- Single-mover carrier: only `g` has the one determination. -/
def onlyGHas (a : JB) (_ : Unit) : Prop := a = .g

/-- Single-mover carrier where every being is really individuated: `g` has the
one pure determination, every other being only its own non-pure thisness. -/
def individuatedHas (a : JB) : JB ⊕ Unit → Prop :=
  Sum.rec (motive := fun _ => Prop) (fun b => a = b ∧ ¬ a = .g) (fun _ => a = .g)

def unitPure : JB ⊕ Unit → Prop :=
  Sum.rec (motive := fun _ => Prop) (fun _ => False) (fun _ => True)

/-- Finite interpretations only: satisfiability of the encoded bundles, not
metaphysical possibility.
* Bare rival: the unchanged part-free model satisfies unrestricted perfection and
  strict pure actuality with two barely distinct first movers.
* Without strict pure actuality: real non-pure thisnesses individuate the roots.
* Without unrestricted perfection: thisnesses count as pure perfections, but each
  root lacks the other's (ordinary immaterial simplicity).
* On the single-mover carrier, unrestricted perfection, strict pure actuality,
  real thisness and at-most-one hold while identity of real indiscernibles fails,
  so that principle exceeds what uniqueness needs; with no determinations at all,
  at-most-one holds and real thisness fails, so real thisness is not an
  equivalent of uniqueness.
* Positive witness: all premises of both uniqueness theorems with an actual
  first mover. -/
def Certificate : Prop :=
  -- bare rival on the unchanged part-free model
  (FirstMoverHasEveryPureDetermination moved moves actHas allPure ∧
    FirstMoverDeterminationsArePure moved moves actHas allPure ∧
    BarelyDistinctFirstMovers moved moves actHas ∧
    ¬ FirstMoverHasRealThisness moved moves actHas ∧
    ¬ RealDeterminationsIndividuate actHas ∧
    ¬ AtMostOneFirstUnmovedMover moved moves) ∧
  -- strict pure actuality omitted: thisness as a non-pure individuating principle
  (FirstMoverHasEveryPureDetermination moved moves thisHas actOnly ∧
    ¬ FirstMoverDeterminationsArePure moved moves thisHas actOnly ∧
    FirstMoverHasRealThisness moved moves thisHas ∧
    RealDeterminationsIndividuate thisHas ∧
    ¬ FirstMoversReallyIndiscernible moved moves thisHas ∧
    ¬ AtMostOneFirstUnmovedMover moved moves) ∧
  -- unrestricted perfection omitted: thisness as a perfection one root lacks
  (¬ FirstMoverHasEveryPureDetermination moved moves thisHas everyPure ∧
    FirstMoverDeterminationsArePure moved moves thisHas everyPure ∧
    FirstMoverHasRealThisness moved moves thisHas ∧
    RealDeterminationsIndividuate thisHas ∧
    ¬ FirstMoversReallyIndiscernible moved moves thisHas ∧
    ¬ AtMostOneFirstUnmovedMover moved moves) ∧
  -- identity of real indiscernibles exceeds uniqueness
  (FirstMoverHasEveryPureDetermination jMoved jMoves onlyGHas (fun _ => True) ∧
    FirstMoverDeterminationsArePure jMoved jMoves onlyGHas (fun _ => True) ∧
    FirstMoverHasRealThisness jMoved jMoves onlyGHas ∧
    AtMostOneFirstUnmovedMover jMoved jMoves ∧
    ¬ RealDeterminationsIndividuate onlyGHas) ∧
  -- real thisness is not an equivalent of uniqueness
  (FirstMoverHasEveryPureDetermination jMoved jMoves (fun (_ : JB) (_ : Empty) => False)
      (fun _ => True) ∧
    FirstMoverDeterminationsArePure jMoved jMoves (fun (_ : JB) (_ : Empty) => False)
      (fun _ => True) ∧
    AtMostOneFirstUnmovedMover jMoved jMoves ∧
    IsFirstUnmovedMover jMoved jMoves (.g : JB) ∧
    ¬ FirstMoverHasRealThisness jMoved jMoves (fun (_ : JB) (_ : Empty) => False)) ∧
  -- nonvacuity
  (FirstMoverHasEveryPureDetermination jMoved jMoves individuatedHas unitPure ∧
    FirstMoverDeterminationsArePure jMoved jMoves individuatedHas unitPure ∧
    FirstMoverHasRealThisness jMoved jMoves individuatedHas ∧
    RealDeterminationsIndividuate individuatedHas ∧
    IsFirstUnmovedMover jMoved jMoves (.g : JB))

end Control
end TruthCore.Causality.PureActThisness
