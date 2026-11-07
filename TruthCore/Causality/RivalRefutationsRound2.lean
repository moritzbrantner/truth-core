module

public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Alternatives.Inertia
public import TruthCore.Alternatives.MegarianMovedPotencyBoundary
public import TruthCore.Greek.Aristotle.MetaphysicsIX

/-! Conditional refutations of three Prima/Secunda Via rivals from premises
deeper than the premise each rivals

* The occasionalist rival `STMT-OCCASIONALIST-MOVER-LINK-WITHOUT-CAUSE` (some
  per se mover link is no per se cause link) fails given three premises: a per
  se mover link is a moving by a mover that is itself moved
  (`PerSeMoverLinkIsMovingByMovedMoverReading`), whatever moves another in a
  respect efficiently causes it in that respect
  (`MoverIsEfficientCauseReading`), and the Second Way's per se ordering
  premise (`SecondEfficientCausesCauseOnlyAsCausedReading`). The occasionalist,
  for whom a creaturely mover is only an occasion, must deny the second.
* The exact countertuple `STMT-ACTUAL-MOVED-NOT-POTENT-COUNTERTUPLE` (something
  is moved in a respect without being in potency in it) fails given three
  Aristotelian analyses: what is being moved to `r` is able to be `r`
  (Metaphysics IX.3), is not yet `r` (Physics III.2), and potency is
  unactualized capacity (Metaphysics IX.6). This route does not use the Physics
  III.1 analysis that refutes the sibling rival `STMT-MOVED-WITHOUT-POTENCY`.
* The inertial rival `STMT-INERTIAL-UNIFORM-MOTION-WITHOUT-MOVER` fails given
  the state reading of uniform motion
  (`UniformPerseveranceIsNotBeingMovedReading`) and the open bridge that a body
  in uniform rectilinear motion which nothing moves in that respect perseveres
  in it (`MoverlessUniformMotionIsPerseveranceReading`). The rival must take the
  becoming reading, or deny that such a body perseveres.

Every refutation is conditional: its premises are open, so it does not count for
closure. Analyst formulations; attribution deferred. -/

@[expose] public section

namespace TruthCore.Causality.RivalRefutationsRound2
open TruthCore.Alternatives.ActPotencyRegress
  (MoverLinkWithoutCauseLinkReading UniformMotionWithoutMoverReading
    MovedIsAbleToBeReading MovedNotYetInActReading)

/-! ## New open premises -/

/-- Open bridge, analyst formulation (attribution deferred): whatever moves
another in a respect is an efficient cause of it in that respect. It links the
*prima via*'s `MovesIn` to the *secunda via*'s `EfficientlyCausesIn`, which
`DEF-EFFICIENT-CAUSING` keeps distinct. It is motivated by Aristotle's mover
mode of cause, the source of change (*Physics* II.3, `DEF-ARISTOTELIAN-CAUSE-MODES`);
the occasionalist denies it of creaturely movers. -/
def MoverIsEfficientCauseReading {B R : Type}
    (MovesIn EfficientlyCausesIn : B → B → R → Prop) : Prop :=
  ∀ y x r, MovesIn y x r → EfficientlyCausesIn y x r

/-- Open analysis, analyst formulation (attribution deferred): a per se link of a
mover series (`MovesAsMoved y x`) is a moving of `x` by a distinct mover `y` in
some respect, while `y` is itself moved by something in some respect. It is the
converse direction of `SecondMoversMoveOnlyAsMovedReading`, which gives only a
sufficient condition for a per se link (`DEF-PER-SE-ORDERED-SERIES`: a link
whose mover moves insofar as it is moved by an upstream mover). -/
def PerSeMoverLinkIsMovingByMovedMoverReading {B R : Type}
    (MovesIn : B → B → R → Prop) (MovesAsMoved : B → B → Prop) : Prop :=
  ∀ y x, MovesAsMoved y x → y ≠ x ∧ (∃ r, MovesIn y x r) ∧ ∃ z r', MovesIn z y r'

/-- Open bridge, analyst formulation (attribution deferred): a body that is in
uniform rectilinear motion in a respect, with nothing moving it in that respect,
perseveres in that motion. Newton's Lex I and Def. III motivate it (the
inertial case of perseverance); the hypothesis is stated with the case's
`MovedIn`, since the vocabulary has no other predicate for being in motion. -/
def MoverlessUniformMotionIsPerseveranceReading {B R : Type}
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (UniformLocalMotion : R → Prop) (Perseveres : B → R → Prop) : Prop :=
  ∀ x r, UniformLocalMotion r → MovedIn x r → (∀ y, ¬ MovesIn y x r) → Perseveres x r

/-! ## Negations of the rivals, on the same predicates -/

/-- The occasionalist rival fails: every per se mover link is a per se cause link. -/
def NoMoverLinkWithoutCauseLink {B : Type} (MovesAsMoved CausesAsCaused : B → B → Prop) :
    Prop :=
  ¬ MoverLinkWithoutCauseLinkReading MovesAsMoved CausesAsCaused

/-- The exact moved-not-potent countertuple fails. -/
def NoMovedNotPotentCountertuple {B R : Type} (MovedIn InPotency : B → R → Prop) : Prop :=
  ¬ TruthCore.Alternatives.MegarianMovedPotencyBoundary.Countertuple MovedIn InPotency

/-- The inertial rival fails: nothing is being moved uniformly in a straight
line with nothing moving it in that respect. -/
def NoUniformMotionWithoutMover {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (UniformLocalMotion : R → Prop) : Prop :=
  ¬ UniformMotionWithoutMoverReading MovedIn MovesIn UniformLocalMotion

namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae (SecondEfficientCausesCauseOnlyAsCausedReading)
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Alternatives.Inertia (UniformPerseveranceIsNotBeingMovedReading)

def yes1 (_ : Unit) : Prop := True
def yes2 (_ _ : Unit) : Prop := True
def no2 (_ _ : Unit) : Prop := False
def yes3 (_ _ _ : Unit) : Prop := True
def no3 (_ _ _ : Unit) : Prop := False

/-- Two distinct beings, each moving (and causing) the other. -/
def diff (y x : Bool) : Prop := y = !x

def diff3 (y x : Bool) (_ : Unit) : Prop := diff y x
def noB2 (_ _ : Bool) : Prop := False
def noB3 (_ _ : Bool) (_ : Unit) : Prop := False

/-- Omission controls. For each refutation and each of its premises, a finite
interpretation keeps the other premises, fails that premise and satisfies the
rival; and each refutation's premises hold together in a model where the
relevant relation is nonempty. Logical models only. -/
def Certificate : Prop :=
  -- occasionalist link: drop the link analysis, the mover/efficient-cause bridge,
  -- the Second Way ordering premise; then all three together
  ((¬ PerSeMoverLinkIsMovingByMovedMoverReading no3 yes2 ∧
      MoverIsEfficientCauseReading no3 no3 ∧
      SecondEfficientCausesCauseOnlyAsCausedReading no3 no2 ∧
      MoverLinkWithoutCauseLinkReading yes2 no2) ∧
    (PerSeMoverLinkIsMovingByMovedMoverReading diff3 diff ∧
      ¬ MoverIsEfficientCauseReading diff3 noB3 ∧
      SecondEfficientCausesCauseOnlyAsCausedReading noB3 noB2 ∧
      MoverLinkWithoutCauseLinkReading diff noB2) ∧
    (PerSeMoverLinkIsMovingByMovedMoverReading diff3 diff ∧
      MoverIsEfficientCauseReading diff3 diff3 ∧
      ¬ SecondEfficientCausesCauseOnlyAsCausedReading diff3 noB2 ∧
      MoverLinkWithoutCauseLinkReading diff noB2) ∧
    (PerSeMoverLinkIsMovingByMovedMoverReading diff3 diff ∧
      MoverIsEfficientCauseReading diff3 diff3 ∧
      SecondEfficientCausesCauseOnlyAsCausedReading diff3 diff ∧
      diff true false)) ∧
  -- countertuple: drop IX.3, III.2, IX.6 (arguments MovedIn InAct InPotency CanBe);
  -- then all three together with something moved
  ((¬ MovedIsAbleToBeReading yes2 no2 ∧ MovedNotYetInActReading yes2 no2 ∧
      PotencyIsUnactualizedCapacityReading no2 no2 no2 ∧
      TruthCore.Alternatives.MegarianMovedPotencyBoundary.Countertuple yes2 no2) ∧
    (MovedIsAbleToBeReading yes2 yes2 ∧ ¬ MovedNotYetInActReading yes2 yes2 ∧
      PotencyIsUnactualizedCapacityReading yes2 no2 yes2 ∧
      TruthCore.Alternatives.MegarianMovedPotencyBoundary.Countertuple yes2 no2) ∧
    (MovedIsAbleToBeReading yes2 yes2 ∧ MovedNotYetInActReading yes2 no2 ∧
      ¬ PotencyIsUnactualizedCapacityReading no2 no2 yes2 ∧
      TruthCore.Alternatives.MegarianMovedPotencyBoundary.Countertuple yes2 no2) ∧
    (MovedIsAbleToBeReading yes2 yes2 ∧ MovedNotYetInActReading yes2 no2 ∧
      PotencyIsUnactualizedCapacityReading no2 yes2 yes2 ∧ yes2 () ())) ∧
  -- inertial rival: drop the state reading, the perseverance bridge; then both
  -- together with a uniformly moved body that has a mover
  ((¬ UniformPerseveranceIsNotBeingMovedReading yes2 yes1 yes2 ∧
      MoverlessUniformMotionIsPerseveranceReading yes2 no3 yes1 yes2 ∧
      UniformMotionWithoutMoverReading yes2 no3 yes1) ∧
    (UniformPerseveranceIsNotBeingMovedReading yes2 yes1 no2 ∧
      ¬ MoverlessUniformMotionIsPerseveranceReading yes2 no3 yes1 no2 ∧
      UniformMotionWithoutMoverReading yes2 no3 yes1) ∧
    (UniformPerseveranceIsNotBeingMovedReading yes2 yes1 no2 ∧
      MoverlessUniformMotionIsPerseveranceReading yes2 yes3 yes1 no2 ∧
      yes2 () () ∧ yes3 () () ()))

end Control
end TruthCore.Causality.RivalRefutationsRound2
