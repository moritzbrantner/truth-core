import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPriorFromIncorruptible

/-!
Facts about deriving act's simple priority from the incorruptible beings of
*Met.* Θ.8 and *In Metaph.* IX, lect. 9 (#352). The omission models use
`Unit` or `Bool` as beings (`true` the incorruptible being, `false` the
corruptible one) and `Unit` as the one respect, `esse`. The root model has a
first mover `f` and a moved thing `m`, and respects `h` (heat), `k` (place) and
`e` (*esse*). Every model is written as exhaustive matches, so the proofs need
no axioms.
-/

namespace TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.ActPriorFromIncorruptible
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam

/-- `true` and only `true`. -/
def isT : Bool → Prop := fun x => match x with | true => True | false => False

/-- `false` and only `false`. -/
def isF : Bool → Prop := fun x => match x with | true => False | false => True

/-- `true` before `false`, and nothing else. -/
def tBeforeF : Bool → Bool → Prop :=
  fun y x => match y, x with
    | true, false => True | true, true => False
    | false, true => False | false, false => False

/-! The root model: `f`, actually hot, heats `m`, which is in potency to heat.
`f` is incorruptible simply, in act in heat and in being, and in potency to a
place `k` in which it is not moved; `m` can fail to be, to be hot and to be at
`k`'s place. -/
namespace Root

inductive B | f | m
inductive R | h | k | e

def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .f, .h => True | .f, .k => False | .f, .e => True
    | .m, .h => False | .m, .k => False | .m, .e => True

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .f, .h => False | .f, .k => True | .f, .e => False
    | .m, .h => True | .m, .k => False | .m, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .f, .h => False | .f, .k => False | .f, .e => False
    | .m, .h => True | .m, .k => False | .m, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .f, .m, .h => True | .f, .m, .k => False | .f, .m, .e => False
    | .f, .f, _ => False | .m, _, _ => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .f, .m => True | .f, .f => False | .m, _ => False

def canFailToBe : B → R → Prop :=
  fun x r => match x, r with
    | .f, .h => False | .f, .k => True | .f, .e => False
    | .m, _ => True

def movesAsMoved : B → B → Prop := fun _ _ => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, inAct, movesAsMoved⟩

end Root

/-- Facts about the incorruptible route to act's simple priority: the pure-act
corollary, the substance derivation, an omission model for each of its five
premises, a model of all five, the first being's substance, and the root model
(`Root`) in which a first mover moved by none, first being and incorruptible,
has a dormant potency in place. No premises. -/
theorem actPriorFromIncorruptibleFacts : ActPriorFromIncorruptibleFacts := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) cannot fail to be in any respect, so pure act
    intro Being Respect InPotency CanFailToBe h1 f hf r hp
    exact hf r (h1 f r hp)
  · -- (2) the substance derivation
    intro Being Respect esse InAct InPotency CanFailToBe PriorInSubstance PriorSimply
      h1 h2 h3 hE hB x hx
    obtain ⟨e, he⟩ := hE
    exact ⟨e, h3 e he, hB e x (h2 e x he (h1 x esse hx))⟩
  · -- (3) without "every potency is of the contradictory": one being, in act and
    -- in potency in being, which cannot fail to be
    intro hAll
    have hT := hAll Unit Unit () (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => False) (fun _ _ => False)
      (fun _ _ _ h => h) (fun _ _ => trivial) ⟨(), fun h => h⟩ (fun _ _ h => h)
    obtain ⟨_, _, h⟩ := hT () trivial
    exact h
  · -- (4) without the priority in substance: no priority at all
    intro hAll
    have hT := hAll Bool Unit () (fun x _ => isT x) (fun x _ => isF x) (fun x _ => isF x)
      (fun _ _ => False) (fun _ _ => False)
      (fun _ _ h => h)
      (by intro e he; cases e <;> first | exact trivial | exact False.elim (he trivial))
      ⟨true, fun h => h⟩ (fun _ _ h => h)
    obtain ⟨_, _, h⟩ := hT false trivial
    exact h
  · -- (5) without the act of the incorruptible: nothing is in act
    intro hAll
    have hT := hAll Bool Unit () (fun _ _ => False) (fun x _ => isF x) (fun x _ => isF x)
      tBeforeF tBeforeF
      (fun _ _ h => h)
      (by intro e p he hp; cases e <;> cases p <;> first | exact trivial | exact False.elim (he trivial) | exact False.elim hp)
      ⟨true, fun h => h⟩ (fun _ _ h => h)
    obtain ⟨_, h, _⟩ := hT false trivial
    exact h
  · -- (6) without an incorruptible being: everything can fail to be
    intro hAll
    have hT := hAll Unit Unit () (fun _ _ => False) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => False) (fun _ _ => False)
      (fun _ _ _ => trivial)
      (fun _ _ he _ => False.elim (he trivial))
      (fun _ he => False.elim (he trivial))
      (fun _ _ h => h)
    obtain ⟨_, h, _⟩ := hT () trivial
    exact h
  · -- (7) without the bridge: prior in substance, not simply prior
    intro hAll
    have hT := hAll Bool Unit () (fun x _ => isT x) (fun x _ => isF x) (fun x _ => isF x)
      tBeforeF (fun _ _ => False)
      (fun _ _ h => h)
      (by intro e p he hp; cases e <;> cases p <;> first | exact trivial | exact False.elim (he trivial) | exact False.elim hp)
      (by intro e he; cases e <;> first | exact trivial | exact False.elim (he trivial))
      ⟨true, fun h => h⟩
    obtain ⟨_, _, h⟩ := hT false trivial
    exact h
  · -- (8) all five, with non-simultaneity, and a potency in being
    refine ⟨Bool, Unit, (), fun x _ => isT x, fun x _ => isF x, fun x _ => isF x,
      tBeforeF, tBeforeF, fun _ _ h => h, ?_, ?_, ⟨true, fun h => h⟩, fun _ _ h => h, ?_,
      ⟨false, trivial⟩⟩
    · intro e p he hp; cases e <;> cases p <;> first | exact trivial | exact False.elim (he trivial) | exact False.elim hp
    · intro e he; cases e <;> first | exact trivial | exact False.elim (he trivial)
    · intro x _ h; cases x <;> first | exact h.1 | exact h.2
  · -- (9) the restricted priority excludes potency in being from a first being
    intro Being Respect esse InAct InPotency PriorSimply hN hP f hf hp
    obtain ⟨y, hy, hyp⟩ := hP f hp
    have hEq : y = f := hf y hyp
    subst hEq
    exact hN y esse ⟨hy, hp⟩
  · -- (10) `Root`
    refine ⟨Root.model, Root.canFailToBe, Root.priorSimply, ⟨Root.B.m, Root.R.h, trivial⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨Root.B.f, fun h => h⟩,
      fun _ _ h => h, ?_, ?_⟩
    · intro x; constructor; intro y h; exact False.elim h
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨Root.B.f, trivial⟩
    · intro y x r h; cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2
    · intro y x r hne hm hmv
      obtain ⟨r', hm'⟩ := hmv
      cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial
    · intro y x r hp hm ha hne; cases y <;> cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact False.elim ha | exact absurd rfl hne | exact trivial
    · intro x r hp hm; cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact ⟨Root.B.f, trivial, trivial⟩
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial
    · intro e p he hp; cases e <;> cases p <;> first | exact trivial | exact False.elim (he trivial) | exact False.elim hp
    · intro e he; cases e <;> first | exact trivial | exact False.elim (he trivial)
    · intro h
      obtain ⟨y, hy, _⟩ := h Root.B.f Root.R.k trivial
      cases y <;> exact hy
    · refine ⟨Root.B.f, ⟨⟨Root.B.m, Root.R.h, trivial⟩, ?_⟩, ?_, fun h => h, Root.R.k, ?_,
        trivial, fun h => h⟩
      · intro r h; cases r <;> exact h
      · intro y h; cases y <;> first | exact False.elim h | rfl
      · intro h; cases h

end TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.ActPriorFromIncorruptible
