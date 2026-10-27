import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPriorFromMotion
import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels

/-!
Facts about deriving act's simple priority from motion (#352). Beings `a`, `b`,
`c` and respects `h` (heat), `k` (another respect), `e` (*esse*) are reused from
`ActPotencyModels`. Each model below is written as exhaustive, non-overlapping
matches, so the proofs need no axioms.
-/

namespace TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.ActPriorFromMotion
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels (B R)

/-! The base world: `a`, actually hot, heats `b`, which is in potency to heat; `a` is simply prior to `b`. Every potency is being actualized. -/
namespace Base

def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def movesAsMoved : B → B → Prop := fun _ _ => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, inAct, movesAsMoved⟩

end Base

/-! The base world, and `a` is also in potency to `k`, in which nothing is moved or in act: drops "every potency is being actualized". `a` is the first mover moved by none and a first being. -/
namespace Dormant

def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => True | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def movesAsMoved : B → B → Prop := fun _ _ => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, inAct, movesAsMoved⟩

end Dormant

/-! `b` is in potency to heat and being heated, by nothing: drops "whatever is moved has a mover". -/
namespace NoMover

def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => False | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def movesAsMoved : B → B → Prop := fun _ _ => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, inAct, movesAsMoved⟩

end NoMover

/-! `a` heats `b` without being hot: drops "a mover is in act". -/
namespace NotInAct

def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def movesAsMoved : B → B → Prop := fun _ _ => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, inAct, movesAsMoved⟩

end NotInAct

/-! `b` heats itself while actually hot and in potency to heat: drops non-simultaneity. -/
namespace Simul

def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => False | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => True | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def movesAsMoved : B → B → Prop := fun _ _ => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, inAct, movesAsMoved⟩

end Simul

/-! The base world without simple priority: drops the actual mover's priority. -/
namespace NoPrior

def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def movesAsMoved : B → B → Prop := fun _ _ => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, inAct, movesAsMoved⟩

end NoPrior

/-- Facts about the motion route to act's simple priority: the derivation, an
omission countermodel for each of its five premises (`Dormant`, `NoMover`,
`NotInAct`, `Simul`, `NoPrior`), a model of all five (`Base`), the restricted
priority without the new premise, and a model (`Dormant`) of every *prima via*
premise, the mover-priority bridge and the restricted priority in which the
first mover moved by none is a first being in potency. No premises. -/
theorem actPriorFromMotionFacts : ActPriorFromMotionFacts := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the derivation
    intro M hA hM hI hN hP x r hp
    obtain ⟨y, hy⟩ := hM x r (hA x r hp)
    have hya := hI y x r hy
    refine ⟨y, hya, hP y x r hp hy hya ?_⟩
    intro hyx
    subst hyx
    exact hN y r ⟨hya, hp⟩
  · -- (2) without "every potency is being actualized": `Dormant`
    intro hAll
    have hT := hAll Dormant.model
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro y x r hp hm ha hne; cases y <;> cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact False.elim ha | exact absurd rfl hne | exact trivial)
    obtain ⟨y, hy, hp⟩ := hT B.a R.k trivial
    cases y <;> first | exact False.elim hy | exact False.elim hp
  · -- (3) without "whatever is moved has a mover": `NoMover`
    intro hAll
    have hT := hAll NoMover.model
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro y x r hp hm ha hne; cases y <;> cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact False.elim ha | exact absurd rfl hne | exact trivial)
    obtain ⟨y, hy, hp⟩ := hT B.b R.h trivial
    cases y <;> first | exact False.elim hy | exact False.elim hp
  · -- (4) without "a mover is in act": `NotInAct`
    intro hAll
    have hT := hAll NotInAct.model
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro y x r hp hm ha hne; cases y <;> cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact False.elim ha | exact absurd rfl hne | exact trivial)
    obtain ⟨y, hy, hp⟩ := hT B.b R.h trivial
    cases y <;> first | exact False.elim hy | exact False.elim hp
  · -- (5) without non-simultaneity: `Simul`
    intro hAll
    have hT := hAll Simul.model
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.b, trivial⟩)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial)
      (by intro y x r hp hm ha hne; cases y <;> cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact False.elim ha | exact absurd rfl hne | exact trivial)
    obtain ⟨y, hy, hp⟩ := hT B.b R.h trivial
    cases y <;> first | exact False.elim hy | exact False.elim hp
  · -- (6) without the actual mover's priority: `NoPrior`
    intro hAll
    have hT := hAll NoPrior.model
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
    obtain ⟨y, hy, hp⟩ := hT B.b R.h trivial
    cases y <;> first | exact False.elim hy | exact False.elim hp
  · -- (7) all five hold in `Base`, with motion and a potency
    refine ⟨Base.model, ?_, ?_, ?_, ?_, ?_, ⟨B.b, R.h, trivial⟩, ⟨B.b, R.h, trivial⟩⟩
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩
    · intro y x r h; cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2
    · intro y x r hp hm ha hne; cases y <;> cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact False.elim ha | exact absurd rfl hne | exact trivial
  · -- (8) the restricted priority without the new premise
    intro M hM hI hN hP x r hp hm
    obtain ⟨y, hy⟩ := hM x r hm
    have hya := hI y x r hy
    refine ⟨y, hya, hP y x r hp hy hya ?_⟩
    intro hyx
    subst hyx
    exact hN y r ⟨hya, hp⟩
  · -- (9) `Dormant`: a first mover moved by none and first being, in potency to `k`
    refine ⟨Dormant.model, ⟨B.b, R.h, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; constructor; intro y h; exact False.elim h
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact trivial
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩
    · intro y x r h; cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial
    · intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2
    · intro y x r hne hm hmv
      obtain ⟨r', hm'⟩ := hmv
      cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne
    · intro y x r hp hm ha hne; cases y <;> cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact False.elim ha | exact absurd rfl hne | exact trivial
    · intro x r hp hm; cases x <;> cases r <;> first | exact False.elim hp | exact False.elim hm | exact ⟨B.a, trivial, trivial⟩
    · exact ⟨B.a, R.k, trivial, fun h => h⟩
    · refine ⟨B.a, ⟨⟨B.b, R.h, trivial⟩, ?_⟩, ?_, ?_⟩
      · intro r h; cases r <;> exact h
      · intro y h; cases y <;> first | exact False.elim h | rfl
      · intro h; exact h R.k trivial
  · -- (10) the new premise contradicts the dormant potency
    intro M hA hD
    obtain ⟨x, r, hp, hn⟩ := hD
    exact hn (hA x r hp)
  · -- (11) as a law of every situation, it contradicts Physics III.1, 201b8-9
    intro Situation Being Respect InPotencyAt MovedInAt hA hC
    obtain ⟨s, x, r, hp, hn⟩ := hC
    exact hn (hA s x r hp)

end TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.ActPriorFromMotion
