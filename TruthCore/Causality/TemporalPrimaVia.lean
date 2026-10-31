import TruthCore.Causality.TemporalActualization
import TruthCore.Case.Catholicism.StageOne
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-! The prima via's vocabulary carries no time index; its module reads every
predicate *simul*, at one time. These analyst definitions instantiate that
vocabulary at each time of a supplied clock, over #700's event profiles. Nothing
here is a source reading. A first mover "at t" is unmoved at t only. -/
namespace TruthCore.Causality.TemporalPrimaVia
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.TemporalActualization
open TruthCore.Case.Catholicism

/-- The canonical reduction premise at each supplied time. -/
def SliceReduction {B R T : Type} (Moved : T → B → R → Prop)
    (Moves : T → B → B → R → Prop) : Prop :=
  ∀ t, ReducedOnlyByAMoverReading (Moved t) (Moves t)

/-- The canonical strong per se premise at each supplied time. -/
def SliceSecondMovers {B R T : Type} (Moved : T → B → R → Prop)
    (Moves : T → B → B → R → Prop) (Link : T → B → B → Prop) : Prop :=
  ∀ t, SecondMoversMoveOnlyAsMovedReading (Moved t) (Moves t) (Link t)

/-- Open bridge from the per se link to event edges: a link y→x at t is carried
by a causal edge from a y-token to an x-token, both exercised at t. The converse
is not asserted, and an edge need not be a link. -/
def LinkOnSimultaneousEdge {E B T : Type} (clock : E → T) (bearer : E → B)
    (C : E → E → Prop) (Link : T → B → B → Prop) : Prop :=
  ∀ t y x, Link t y x →
    ∃ e f, C e f ∧ bearer e = y ∧ bearer f = x ∧ clock e = t ∧ clock f = t

/-- The canonical regress premise at every time, required only if some event
edge is simultaneous. -/
def RegressIfSimultaneous {E B T : Type} (clock : E → T) (C : E → E → Prop)
    (Link : T → B → B → Prop) : Prop :=
  HasSimultaneous clock C → ∀ t, NoInfinitePerSeMoverSeriesReading (Link t)

/-- The route consequence. At each time at which something is moved, a mover
unmoved at that time cannot be lacking; there is no finite event cycle; and either
all edges are strictly forward and each mover of another at t is unmoved at t, or
no edge is backward and some edge is simultaneous. No conclusion about a being
unmoved at every time, or about well-foundedness of the event relation. -/
def SliceRouteOutcome {E B R T : Type} [LT T] (clock : E → T) (C : E → E → Prop)
    (Moved : T → B → R → Prop) (Moves : T → B → B → R → Prop) : Prop :=
  (∀ t, SomethingIsMovedReading (Moved t) →
    FirstUnmovedMoverCannotBeLackingReading (Moved t) (Moves t)) ∧
  EventAcyclic C ∧
  ((StrictForward clock C ∧ ∀ t y x r, y ≠ x → Moves t y x r → ∀ r', ¬ Moved t y r') ∨
    (NoBackward clock C ∧ HasSimultaneous clock C))

/-- A universal conditional: under strict forwardness, the link bridge, the per se
premise and the pure-act premise at each time, a mover of another at t has no
potency in any respect at t. -/
def StrictPureActConflict : Prop :=
  ∀ (E B R T : Type) [Preorder T] (clock : E → T) (bearer : E → B) (C : E → E → Prop)
    (Moved Potency : T → B → R → Prop) (Moves : T → B → B → R → Prop)
    (Link : T → B → B → Prop),
    StrictForward clock C → LinkOnSimultaneousEdge clock bearer C Link →
    SliceSecondMovers Moved Moves Link →
    (∀ t, FirstUnmovedMoverIsPureAct (Moved t) (Moves t) (PureAct (Potency t))) →
    ∀ t y x r, y ≠ x → Moves t y x r → ∀ s, ¬ Potency t y s

/-- Every premise of the route theorem except `RegressIfSimultaneous`, for the
models below. -/
def LocalRoutePremises {E B R T : Type} [LT T] (clock : E → T) (bearer : E → B)
    (respect : E → R) (C : E → E → Prop) (Moves : T → B → B → R → Prop)
    (Moved Actual Potency : T → B → R → Prop) (Link : T → B → B → Prop) : Prop :=
  NoBackward clock C ∧ MotionProjection clock bearer respect C Moves ∧
  LocatedMotion Moves Moved ∧ PotentialMotion Moved Potency ∧ ActualMover Moves Actual ∧
  NotBoth Actual Potency ∧ SliceReduction Moved Moves ∧ SliceSecondMovers Moved Moves Link ∧
  LinkOnSimultaneousEdge clock bearer C Link

/-- A₀→B₁→A₂ at clocks 0, 1, 2 with two respects. A has its potency for the
later respect already at t = 1. All predicates are stipulated. -/
def fbRespect (e : Fin 3) : Bool := decide (e.val = 2)
def fbClock (e : Fin 3) : ℤ := e.val
def fbMoves (t : ℤ) (y x r : Bool) : Prop :=
  (t = 1 ∧ y = false ∧ x = true ∧ r = false) ∨ (t = 2 ∧ y = true ∧ x = false ∧ r = true)
def fbMoved (t : ℤ) (x r : Bool) : Prop :=
  (t = 1 ∧ x = true ∧ r = false) ∨ (t = 2 ∧ x = false ∧ r = true)
def fbActual (t : ℤ) (y r : Bool) : Prop :=
  (t = 1 ∧ y = false ∧ r = false) ∨ (t = 2 ∧ y = true ∧ r = true)
def fbPotency (t : ℤ) (x r : Bool) : Prop :=
  fbMoved t x r ∨ (t = 1 ∧ x = false ∧ r = true)

/-- n+1's token causes n's token, at clock -n; each number is moved at one time. -/
def dClock (n : ℕ) : ℤ := -(n : ℤ)
def dC (y x : ℕ) : Prop := y = x + 1
def dMoves (t : ℤ) (y x : ℕ) (_ : Unit) : Prop := t = -(x : ℤ) ∧ y = x + 1
def dMoved (t : ℤ) (x : ℕ) (_ : Unit) : Prop := t = -(x : ℤ)
def dActual (t : ℤ) (y : ℕ) (_ : Unit) : Prop := t = -(y : ℤ) + 1

/-- The #700 alternating circle with its link at time 0. -/
def circleLink (t : ℤ) (y x : Bool) : Prop := t = 0 ∧ y ≠ x

/-- A simultaneous chain 0→1→2 with 0 unmoved. -/
def chainC (e f : Fin 3) : Prop := e.val + 1 = f.val
def chainClock (_ : Fin 3) : ℤ := 0
def chainMoves (t : ℤ) (y x r : Fin 3) : Prop := t = 0 ∧ y.val + 1 = x.val ∧ r = x
def chainMoved (t : ℤ) (x r : Fin 3) : Prop := t = 0 ∧ r = x ∧ x.val ≠ 0
def chainActual (t : ℤ) (y r : Fin 3) : Prop := t = 0 ∧ y.val + 1 = r.val
def chainLink (t : ℤ) (y x : Fin 3) : Prop := t = 0 ∧ y.val = 1 ∧ x.val = 2

/-- Conditional conflict plus four jointly checked models of the local premises.
(1) Strict feedback: different first movers at t = 1, 2, none unmoved at all times,
and the pure-act premise fails at t = 1. (2) Strict descent: a slice mover at each
event's clock value, yet the event relation is not well-founded. (3) Circle: the local premises hold,
the slice regress premise and the slice conclusion fail. (4) Simultaneous chain: all
premises hold and a first mover exists. Satisfiability only. -/
def Controls : Prop :=
  StrictPureActConflict ∧
  (LocalRoutePremises fbClock feedbackBearer fbRespect feedbackC fbMoves fbMoved fbActual
      fbPotency (fun _ _ _ => False) ∧
    StrictForward fbClock feedbackC ∧
    IsFirstUnmovedMover (fbMoved 1) (fbMoves 1) false ∧
    IsFirstUnmovedMover (fbMoved 2) (fbMoves 2) true ∧
    (¬ ∃ f, (∃ t x r, fbMoves t f x r) ∧ ∀ t r, ¬ fbMoved t f r) ∧
    ¬ FirstUnmovedMoverIsPureAct (fbMoved 1) (fbMoves 1) (PureAct (fbPotency 1))) ∧
  (LocalRoutePremises dClock id (fun _ => ()) dC dMoves dMoved dActual dMoved
      (fun _ _ _ => False) ∧
    StrictForward dClock dC ∧
    (∀ n : ℕ, IsFirstUnmovedMover (dMoved (dClock n)) (dMoves (dClock n)) (n + 1)) ∧
    (∀ e, ∃ f, dC f e) ∧ ¬ WellFounded dC) ∧
  (LocalRoutePremises circleClock id id circleC circleMoves circleMoved circleActual
      circlePotency circleLink ∧
    HasSimultaneous circleClock circleC ∧
    SomethingIsMovedReading (circleMoved 0) ∧
    ¬ NoInfinitePerSeMoverSeriesReading (circleLink 0) ∧
    ¬ FirstUnmovedMoverCannotBeLackingReading (circleMoved 0) (circleMoves 0)) ∧
  (LocalRoutePremises chainClock id id chainC chainMoves chainMoved chainActual chainMoved
      chainLink ∧
    RegressIfSimultaneous chainClock chainC chainLink ∧
    HasSimultaneous chainClock chainC ∧
    IsFirstUnmovedMover (chainMoved 0) (chainMoves 0) 0)

end TruthCore.Causality.TemporalPrimaVia
