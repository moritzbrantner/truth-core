import TruthCore.Case.Catholicism.StageOneBridges
import TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct IsFirstUnmovedMover
  FirstUnmovedMoverIsFirstBeing)

/-- ST I q.3 a.1 co., second proof, for the *prima via*'s mover: if the first
mover moved by none is the first being (open bridge), then, since the first
being is in no way in potency, every first mover moved by none is pure act. Discharges the #159 gap
statement `FirstUnmovedMoverIsPureAct` with `PureAct InPotency` for its
`PureAct` parameter. -/
theorem firstMoverPureAct {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hFirstBeing : FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply)
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency) := by
  -- INF-AQUINAS-ST-I-Q3-A1-FIRST-BEING-NO-POTENCY (result FirstBeingNoPotency)
  have hNoPotency : FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply :=
    FirstBeingNoPotency.firstBeingNoPotency InPotency InAct PriorSimply hPrior hNotBoth
  -- INF-AQUINAS-ST-I-Q3-A1-FIRST-MOVER-PURE-ACT
  intro f hF
  exact hNoPotency f (hFirstBeing f hF)

namespace NonEntailment

inductive B | f | x | z
inductive R | heat | cold

def heat : R → Prop
  | .heat => True
  | .cold => False

def cold : R → Prop
  | .heat => False
  | .cold => True

def movedIn : B → R → Prop
  | .x, r => heat r
  | .f, _ => False
  | .z, _ => False

def movesIn : B → B → R → Prop
  | .f, b, r => match b with
    | .x => heat r
    | .f => False
    | .z => False
  | .x, _, _ => False
  | .z, _, _ => False

def inPotency : B → R → Prop
  | .x, r => heat r
  | .f, r => cold r
  | .z, _ => False

def inAct : B → R → Prop
  | .f, r => heat r
  | .z, r => cold r
  | .x, _ => False

def priorSimply : B → B → Prop
  | .f, b => match b with
    | .x => True
    | .f => False
    | .z => False
  | .z, b => match b with
    | .f => True
    | .x => False
    | .z => False
  | .x, _ => False

def movesAsMoved : B → B → Prop := fun _ _ => False

end NonEntailment

/-- The *prima via*'s premises (#151) together with the act-priority premise do
not yield pure act. In the model, `f` heats `x` and is moved by nothing, yet it is
in potency to cold, a respect in which it moves nothing; `z`, in act as to cold,
is simply prior to `f`. So `FirstUnmovedMoverIsFirstBeing` is not
redundant: "moved by none" does not mean "in potency in no respect". -/
theorem firstWayDoesNotYieldPureAct :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved : Being → Being → Prop)
      (PriorSimply : Being → Being → Prop),
      SomethingIsMovedReading MovedIn →
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency) := by
  open NonEntailment in
  intro h
  have hPure := h B R movedIn movesIn inPotency inAct movesAsMoved priorSimply
    ⟨.x, .heat, trivial⟩
    (by intro b r hm; cases b <;> cases r <;> first | exact hm | exact False.elim hm)
    (by
      intro y b r hm
      cases y <;> cases b <;> cases r <;> first | exact hm | exact False.elim hm)
    (by
      intro b r hm
      cases b <;> cases r
      all_goals first | exact False.elim hm | exact ⟨.f, trivial⟩)
    (by
      intro b r ⟨ha, hp⟩
      cases b <;> cases r <;> first | exact False.elim ha | exact False.elim hp)
    (by
      intro y b r _ hmv ⟨r', hm⟩
      cases y <;> cases b <;> cases r <;> cases r'
      all_goals first | exact False.elim hmv | exact False.elim hm)
    (by intro b; exact Acc.intro _ fun a h => False.elim h)
    (by
      intro b r hp
      cases b <;> cases r
      all_goals first
        | exact False.elim hp
        | exact ⟨.f, trivial, trivial⟩
        | exact ⟨.z, trivial, trivial⟩)
  have hF : IsFirstUnmovedMover movedIn movesIn B.f :=
    ⟨⟨.x, .heat, trivial⟩, fun r hm => by cases r <;> exact hm⟩
  exact hPure .f hF .cold trivial
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct
