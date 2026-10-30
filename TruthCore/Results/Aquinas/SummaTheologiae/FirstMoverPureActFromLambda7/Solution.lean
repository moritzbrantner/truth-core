import TruthCore.Case.Catholicism.StageOne
import TruthCore.Latin.Aquinas.InMetaphysicam.BookXII
import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.ActPriorFromIncorruptible.Solution

/-!
*Metaphysics* Λ.7 and *In Metaph.* XII, lect. 7 as a route to the pure act of the
*prima via*'s first mover that does not apply act's simple priority to an
unmoved being (#352). `ACT-PRIOR-FROM-INCORRUPTIBLE-FACTS` showed that a first
mover moved by none can be first being and incorruptible simply and still have
a dormant potency in a respect other than substance; Λ.7 denies, of the unmoved
mover, any such potency in a respect of change (it cannot be otherwise in any
way, unlike the first heaven, which can be otherwise in place). The proof
composes that result's pure-act corollary.
-/

namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureActFromLambda7
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct IsFirstUnmovedMover
  AtMostOneFirstUnmovedMover)

/-- *Met.* Λ.7 for the *prima via*'s mover, without act's simple priority: some
mover moved in no respect of change and in act in being cannot be otherwise in
any respect of change (Λ.7, 1072b4-10; *In Metaph.* XII, lect. 7 n. 12–13); a
mover unchangeable in every respect of change is unmoved and cannot be otherwise
in any respect (open bridge, unattributed; lect. 11 n. 8 supports it for the
respect of understanding only); there is at most one first mover
moved by none; whatever can fail to be `r` can be otherwise in `r` (open bridge,
unattributed; *In Metaph.* V, lect. 6 n. 14 supports it in part); and every
potency is of the contradictory (Θ.8, 1050b8-15;
*In Metaph.* IX, lect. 9 n. 2–4). Hence every first mover moved by none is pure
act. Not used: act's simple priority, non-simultaneity, and the bridge that the
first unmoved mover is the first being. -/
theorem firstMoverPureActFromLambda7 {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
    (esse : Respect) (OfChange : Respect → Prop)
    (hLambda : SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
      OfChange CanBeOtherwise)
    (hScope : UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
      OfChange CanBeOtherwise)
    (hOne : AtMostOneFirstUnmovedMover MovedIn MovesIn)
    (hBridge : CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise)
    (hContradiction : PotencyIsOfContradictionReading InPotency CanFailToBe) :
    FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency) := by
  intro f hf
  obtain ⟨m, hMoves, hUnmoved, _, hFixed⟩ := hLambda
  have hAll := hScope m hMoves hUnmoved hFixed
  have hfm : f = m := hOne f m hf ⟨hMoves, fun r => (hAll r).1⟩
  subst hfm
  -- The pure-act corollary of ACT-PRIOR-FROM-INCORRUPTIBLE-FACTS (item 1).
  exact ActPotencyFacts.ActPriorFromIncorruptible.actPriorFromIncorruptibleFacts.1
    Being Respect InPotency CanFailToBe hContradiction f
    (fun r hFail => (hAll r).2 (hBridge f r hFail))

/-! Finite models. Predicates are `Bool`-valued and read as `= true`, written as
exhaustive matches, so every check is by `decide` or `rfl` and no axiom is used.
Respects: heat `h`, a place `k`, being `e` (all of change) and `n`, a respect
that is not one of change. -/

/-! `Base`: `f` heats `x` and is moved in no respect; `f` is in potency to the place `k`, in which nothing moves it; `x` is in potency to heat. -/
namespace Base

inductive B | f | x
inductive R | h | k | e | n

def ofChange : R → Bool :=
  fun a => match a with
    | .h => true
    | .k => true
    | .e => true
    | .n => false

def movedIn : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => false
    | .f, .k => false
    | .f, .e => false
    | .f, .n => false
    | .x, .h => true
    | .x, .k => false
    | .x, .e => false
    | .x, .n => false

def movesIn : B → B → R → Bool :=
  fun a b c => match a, b, c with
    | .f, .f, .h => false
    | .f, .f, .k => false
    | .f, .f, .e => false
    | .f, .f, .n => false
    | .f, .x, .h => true
    | .f, .x, .k => false
    | .f, .x, .e => false
    | .f, .x, .n => false
    | .x, .f, .h => false
    | .x, .f, .k => false
    | .x, .f, .e => false
    | .x, .f, .n => false
    | .x, .x, .h => false
    | .x, .x, .k => false
    | .x, .x, .e => false
    | .x, .x, .n => false

def inAct : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => true
    | .f, .k => false
    | .f, .e => true
    | .f, .n => false
    | .x, .h => false
    | .x, .k => false
    | .x, .e => true
    | .x, .n => false

def inPotency : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => false
    | .f, .k => true
    | .f, .e => false
    | .f, .n => false
    | .x, .h => true
    | .x, .k => false
    | .x, .e => false
    | .x, .n => false

def nothing : B → R → Bool := fun _ _ => false

end Base
/-! `Mind`: as `Base`, but `f`'s potency is in `n`, not a respect of change. -/
namespace Mind

inductive B | f | x
inductive R | h | k | e | n

def ofChange : R → Bool :=
  fun a => match a with
    | .h => true
    | .k => true
    | .e => true
    | .n => false

def movedIn : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => false
    | .f, .k => false
    | .f, .e => false
    | .f, .n => false
    | .x, .h => true
    | .x, .k => false
    | .x, .e => false
    | .x, .n => false

def movesIn : B → B → R → Bool :=
  fun a b c => match a, b, c with
    | .f, .f, .h => false
    | .f, .f, .k => false
    | .f, .f, .e => false
    | .f, .f, .n => false
    | .f, .x, .h => true
    | .f, .x, .k => false
    | .f, .x, .e => false
    | .f, .x, .n => false
    | .x, .f, .h => false
    | .x, .f, .k => false
    | .x, .f, .e => false
    | .x, .f, .n => false
    | .x, .x, .h => false
    | .x, .x, .k => false
    | .x, .x, .e => false
    | .x, .x, .n => false

def inAct : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => true
    | .f, .k => false
    | .f, .e => true
    | .f, .n => false
    | .x, .h => false
    | .x, .k => false
    | .x, .e => true
    | .x, .n => false

def inPotency : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => false
    | .f, .k => false
    | .f, .e => false
    | .f, .n => true
    | .x, .h => true
    | .x, .k => false
    | .x, .e => false
    | .x, .n => false

def nothing : B → R → Bool := fun _ _ => false

end Mind
/-! `Two`: two first movers `m` and `g` heat `x`; `g` is in potency to the place `k`. -/
namespace Two

inductive B | m | g | x
inductive R | h | k | e | n

def ofChange : R → Bool :=
  fun a => match a with
    | .h => true
    | .k => true
    | .e => true
    | .n => false

def movedIn : B → R → Bool :=
  fun a b => match a, b with
    | .m, .h => false
    | .m, .k => false
    | .m, .e => false
    | .m, .n => false
    | .g, .h => false
    | .g, .k => false
    | .g, .e => false
    | .g, .n => false
    | .x, .h => true
    | .x, .k => false
    | .x, .e => false
    | .x, .n => false

def movesIn : B → B → R → Bool :=
  fun a b c => match a, b, c with
    | .m, .m, .h => false
    | .m, .m, .k => false
    | .m, .m, .e => false
    | .m, .m, .n => false
    | .m, .g, .h => false
    | .m, .g, .k => false
    | .m, .g, .e => false
    | .m, .g, .n => false
    | .m, .x, .h => true
    | .m, .x, .k => false
    | .m, .x, .e => false
    | .m, .x, .n => false
    | .g, .m, .h => false
    | .g, .m, .k => false
    | .g, .m, .e => false
    | .g, .m, .n => false
    | .g, .g, .h => false
    | .g, .g, .k => false
    | .g, .g, .e => false
    | .g, .g, .n => false
    | .g, .x, .h => true
    | .g, .x, .k => false
    | .g, .x, .e => false
    | .g, .x, .n => false
    | .x, .m, .h => false
    | .x, .m, .k => false
    | .x, .m, .e => false
    | .x, .m, .n => false
    | .x, .g, .h => false
    | .x, .g, .k => false
    | .x, .g, .e => false
    | .x, .g, .n => false
    | .x, .x, .h => false
    | .x, .x, .k => false
    | .x, .x, .e => false
    | .x, .x, .n => false

def inAct : B → R → Bool :=
  fun a b => match a, b with
    | .m, .h => true
    | .m, .k => false
    | .m, .e => true
    | .m, .n => false
    | .g, .h => true
    | .g, .k => false
    | .g, .e => true
    | .g, .n => false
    | .x, .h => false
    | .x, .k => false
    | .x, .e => true
    | .x, .n => false

def inPotency : B → R → Bool :=
  fun a b => match a, b with
    | .m, .h => false
    | .m, .k => false
    | .m, .e => false
    | .m, .n => false
    | .g, .h => false
    | .g, .k => true
    | .g, .e => false
    | .g, .n => false
    | .x, .h => true
    | .x, .k => false
    | .x, .e => false
    | .x, .n => false

def nothing : B → R → Bool := fun _ _ => false

end Two
/-! `Pure`: `f` heats `x` and is in potency in no respect. -/
namespace Pure

inductive B | f | x
inductive R | h | k | e | n

def ofChange : R → Bool :=
  fun a => match a with
    | .h => true
    | .k => true
    | .e => true
    | .n => false

def movedIn : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => false
    | .f, .k => false
    | .f, .e => false
    | .f, .n => false
    | .x, .h => true
    | .x, .k => false
    | .x, .e => false
    | .x, .n => false

def movesIn : B → B → R → Bool :=
  fun a b c => match a, b, c with
    | .f, .f, .h => false
    | .f, .f, .k => false
    | .f, .f, .e => false
    | .f, .f, .n => false
    | .f, .x, .h => true
    | .f, .x, .k => false
    | .f, .x, .e => false
    | .f, .x, .n => false
    | .x, .f, .h => false
    | .x, .f, .k => false
    | .x, .f, .e => false
    | .x, .f, .n => false
    | .x, .x, .h => false
    | .x, .x, .k => false
    | .x, .x, .e => false
    | .x, .x, .n => false

def inAct : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => true
    | .f, .k => false
    | .f, .e => true
    | .f, .n => false
    | .x, .h => false
    | .x, .k => false
    | .x, .e => true
    | .x, .n => false

def inPotency : B → R → Bool :=
  fun a b => match a, b with
    | .f, .h => false
    | .f, .k => false
    | .f, .e => false
    | .f, .n => false
    | .x, .h => true
    | .x, .k => false
    | .x, .e => false
    | .x, .n => false

def nothing : B → R → Bool := fun _ _ => false

end Pure

/-- Facts about the Λ.7 route to pure act.

1. **Each of its five premises is needed.** For each, a model of the other four
   has a first mover moved by none that is in potency in some respect. Without
   the Λ.7 reading, the unique first mover has a dormant potency in place: the
   analogue, for a first mover, of what *In Metaph.* IX, lect. 9 n. 6 allows in
   moved incorruptible bodies. Without the scope bridge, the mover is fixed in
   every respect of change but in potency in a respect that is not one of change.
2. **It is not vacuous.** All five hold in a model with a first mover moved by
   none.
3. **The universal sibling reading needs no uniqueness.** If every mover moved
   in no respect of change and in act in being cannot be otherwise in any
   respect of change, then, with every mover being in act in the respect in
   which it moves (ST I q.2 a.3), actuality only insofar as being (ST I q.4 a.1
   ad 3), the scope bridge, the bridge from failing to be to being otherwise and
   the potency of the contradictory, every first mover moved by none is pure
   act. -/
theorem lambda7RouteFacts :
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (_InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (_esse : Respect) (OfChange : Respect → Prop),
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (∃ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise ∧
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise ∧
      AtMostOneFirstUnmovedMover MovedIn MovesIn ∧
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise ∧
      PotencyIsOfContradictionReading InPotency CanFailToBe ∧
      ∃ f, IsFirstUnmovedMover MovedIn MovesIn f) ∧
    (∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      EveryUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      MovesOnlyAsInActReading MovesIn InAct →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Without the Λ.7 reading: `Base`, `f` can fail to be and be otherwise in place.
    intro h
    have hPure := h Base.B Base.R (fun b r => Base.movedIn b r = true)
      (fun y b r => Base.movesIn y b r = true) (fun b r => Base.inAct b r = true)
      (fun b r => Base.inPotency b r = true) (fun b r => Base.inPotency b r = true)
      (fun b r => Base.inPotency b r = true) Base.R.e (fun r => Base.ofChange r = true)
      (by intro y _ hu hc r; cases y <;> first
        | exact absurd rfl (hc .k rfl) | exact absurd rfl (hu .h rfl))
      (by intro a b ha hb; cases a <;> cases b <;> first
        | rfl | exact absurd rfl (ha.2 .h) | exact absurd rfl (hb.2 .h))
      (fun _ _ h => h) (fun _ _ h => h)
    exact hPure .f ⟨⟨.x, .h, rfl⟩, fun r => by cases r <;> decide⟩ .k rfl
  · -- Without the scope bridge: `Mind`, `f`'s potency is in `n`.
    intro h
    have hPure := h Mind.B Mind.R (fun b r => Mind.movedIn b r = true)
      (fun y b r => Mind.movesIn y b r = true) (fun b r => Mind.inAct b r = true)
      (fun b r => Mind.inPotency b r = true) (fun b r => Mind.inPotency b r = true)
      (fun b r => Mind.inPotency b r = true) Mind.R.e (fun r => Mind.ofChange r = true)
      ⟨.f, ⟨.x, .h, rfl⟩, fun r _ => by cases r <;> decide, rfl,
        fun r hr => by cases r <;> first | decide | exact absurd hr (by decide)⟩
      (by intro a b ha hb; cases a <;> cases b <;> first
        | rfl | exact absurd rfl (ha.2 .h) | exact absurd rfl (hb.2 .h))
      (fun _ _ h => h) (fun _ _ h => h)
    exact hPure .f ⟨⟨.x, .h, rfl⟩, fun r => by cases r <;> decide⟩ .n rfl
  · -- Without uniqueness: `Two`; `m` witnesses Λ.7, `g` has a potency in place.
    intro h
    have hPure := h Two.B Two.R (fun b r => Two.movedIn b r = true)
      (fun y b r => Two.movesIn y b r = true) (fun b r => Two.inAct b r = true)
      (fun b r => Two.inPotency b r = true) (fun b r => Two.inPotency b r = true)
      (fun b r => Two.inPotency b r = true) Two.R.e (fun r => Two.ofChange r = true)
      ⟨.m, ⟨.x, .h, rfl⟩, fun r _ => by cases r <;> decide, rfl,
        fun r _ => by cases r <;> decide⟩
      (by intro y _ hu hc r; cases y <;> first
        | exact absurd rfl (hc .k rfl) | exact absurd rfl (hu .h rfl)
        | (cases r <;> exact ⟨by decide, by decide⟩))
      (fun _ _ h => h) (fun _ _ h => h)
    exact hPure .g ⟨⟨.x, .h, rfl⟩, fun r => by cases r <;> decide⟩ .k rfl
  · -- Without the bridge: `Base`, `f` can fail to be in place but cannot be
    -- otherwise anywhere.
    intro h
    have hPure := h Base.B Base.R (fun b r => Base.movedIn b r = true)
      (fun y b r => Base.movesIn y b r = true) (fun b r => Base.inAct b r = true)
      (fun b r => Base.inPotency b r = true) (fun b r => Base.inPotency b r = true)
      (fun b r => Base.nothing b r = true) Base.R.e (fun r => Base.ofChange r = true)
      ⟨.f, ⟨.x, .h, rfl⟩, fun r _ => by cases r <;> decide, rfl,
        fun r _ => by cases r <;> decide⟩
      (by intro y _ hu _ r; cases y <;> first
        | exact absurd rfl (hu .h rfl)
        | (cases r <;> exact ⟨by decide, by decide⟩))
      (by intro a b ha hb; cases a <;> cases b <;> first
        | rfl | exact absurd rfl (ha.2 .h) | exact absurd rfl (hb.2 .h))
      (fun _ _ h => h)
    exact hPure .f ⟨⟨.x, .h, rfl⟩, fun r => by cases r <;> decide⟩ .k rfl
  · -- Without the potency of the contradictory: `Base`, nothing can fail to be or
    -- be otherwise.
    intro h
    have hPure := h Base.B Base.R (fun b r => Base.movedIn b r = true)
      (fun y b r => Base.movesIn y b r = true) (fun b r => Base.inAct b r = true)
      (fun b r => Base.inPotency b r = true) (fun b r => Base.nothing b r = true)
      (fun b r => Base.nothing b r = true) Base.R.e (fun r => Base.ofChange r = true)
      ⟨.f, ⟨.x, .h, rfl⟩, fun r _ => by cases r <;> decide, rfl,
        fun r _ => by cases r <;> decide⟩
      (by intro y _ hu _ r; cases y <;> first
        | exact absurd rfl (hu .h rfl)
        | (cases r <;> exact ⟨by decide, by decide⟩))
      (by intro a b ha hb; cases a <;> cases b <;> first
        | rfl | exact absurd rfl (ha.2 .h) | exact absurd rfl (hb.2 .h))
      (fun _ _ h => h)
    exact hPure .f ⟨⟨.x, .h, rfl⟩, fun r => by cases r <;> decide⟩ .k rfl
  · -- All five, with a first mover moved by none: `Pure`.
    refine ⟨Pure.B, Pure.R, fun b r => Pure.movedIn b r = true,
      fun y b r => Pure.movesIn y b r = true, fun b r => Pure.inAct b r = true,
      fun b r => Pure.inPotency b r = true, fun b r => Pure.inPotency b r = true,
      fun b r => Pure.inPotency b r = true, Pure.R.e, fun r => Pure.ofChange r = true,
      ?_, ?_, ?_, fun _ _ h => h, fun _ _ h => h,
      ⟨.f, ⟨.x, .h, rfl⟩, fun r => by cases r <;> decide⟩⟩
    · exact ⟨.f, ⟨.x, .h, rfl⟩, fun r _ => by cases r <;> decide, rfl,
        fun r _ => by cases r <;> decide⟩
    · intro y _ hu _ r; cases y <;> first
        | exact absurd rfl (hu .h rfl)
        | (cases r <;> exact ⟨by decide, by decide⟩)
    · intro a b ha hb; cases a <;> cases b <;> first
        | rfl | exact absurd rfl (ha.2 .h) | exact absurd rfl (hb.2 .h)
  · -- The universal sibling reading, without uniqueness.
    intro Being Respect MovedIn MovesIn InAct InPotency CanFailToBe CanBeOtherwise esse
      OfChange hEvery hMover hBeing hScope hBridge hContradiction f hf
    obtain ⟨x, r, hMoves⟩ := hf.1
    have hAct : InAct f esse := hBeing f r (hMover f x r hMoves)
    have hAll := hScope f hf.1 (fun r _ => hf.2 r)
      (hEvery f hf.1 (fun r _ => hf.2 r) hAct)
    exact ActPotencyFacts.ActPriorFromIncorruptible.actPriorFromIncorruptibleFacts.1
      Being Respect InPotency CanFailToBe hContradiction f
      (fun r hFail => (hAll r).2 (hBridge f r hFail))

end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureActFromLambda7
