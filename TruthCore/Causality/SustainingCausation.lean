module

public import TruthCore.Causality.GroundedBeginnings
public import TruthCore.Causality.DeiFiliusImmenseIncomprehensible

/-!
# Sustaining versus originating causation of being, time-indexed

Analyst formulation for the modal spine (`docs/notes/modal-spine.md`).
Attribution deferred: ST I q.104 a.1 motivates the sustaining reading and
q.8 a.1 the contact principle; no claim states any definition or premise below.

The corpus relation `CausesIn c x esse` ("c causes x's being") is tenseless. It
leaves open whether the causing *originates* x's being (acts when x begins and
may then cease, as a builder does for a house) or *sustains* it (acts at every
moment at which x is, as the sun does for the light in the air, q.104 a.1 co.).
Two spine nodes need that difference: the presence step of the immensity sense
bridge (`8bf775e9`, from causing everything's being to being present to
everything now) and the warrant for premise A2ab of Arrival A (`71df1177`, a
beginning has a ground present at the empty moment or later). This module types
the two senses over a temporal `History` and shows what each buys.

**Primitive.** `BeingGiving.GivesAt v c x t`: in history `v`, `c` exercises
causation of `x`'s being at moment `t` (`c` gives `x` being at `t`). Explicitly
identified PRIMITIVE (Encode first). It is the effect-side time index of a
causal activity, not a claim that the agent is in time: q.104 a.1 ad 4 says the
divine conserving action is "without either motion or time", and `GivesAt` at
`t` reads as that action bearing on the creature at `t`. Distinguished from
counterfactual dependence (x would not be at `t` without it), from preventing
corruption (removing a destroyer, q.104 a.1 ad 3), and from the world-level
`Ontic.Causes`. Open obligation: an analysis of the exercise of esse-giving
(productive receipt by this same bearer, definition `56989bd0` note), and of the
dependence that "required at every moment" adds to mere concurrence.

**The two senses** (disambiguation CAUSE_OF_BEING, both overlapping, neither
exhaustive):

* CAUSE_OF_BEING_1, *originating* (`OriginatesBeing`): `c` gives `x` being at
  a first moment of `x`'s presence (`TemporalHistory.BeginsAt`). Nothing is required of
  `c` afterwards. Example: the builder of a house; the parent of a child.
* CAUSE_OF_BEING_2, *sustaining* (`SustainsBeing`): `x` is present at some
  moment and `c` gives `x` being at every moment at which `x` is present.
  Examples: the sun lighting the air ("the air does not continue to be lit up,
  even for a moment, when the sun ceases to act upon it", q.104 a.1 co.); a hand
  holding a stone aloft (the stone's being held, not the stone's being, is
  sustained: a model of the time profile, not an instance of esse-giving).
  Counterexample: the builder, whose house stands after building ceases.

A sustaining cause of a thing with a first moment of presence is also an
originating cause (`originatesOfSustains` in the Solution); the converse fails
(`Control.inertia`). The senses differ in what they require after the
beginning, not only in strength.

**Contact principle** (`GiverPresentWhenGiving`, open): whatever gives a thing
being at `t` is present at `t`. After q.8 a.1: an agent must be joined to that
wherein it acts immediately. Read for a timeless agent as co-presence to the
moment, not temporal location. It excludes action at a temporal distance; it
says nothing about spatial location.

**Structural properties.** `GivesAt` is not assumed transitive, asymmetric,
irreflexive or functional; several sustainers of one thing are allowed. No
linear order, first moment or density of time is assumed; comparability of
moments is an explicit premise (`TimesTrichotomous`) where a route uses it. `SustainsBeing` is not transitive by definition.

**Rival.** Existential inertia (Schmid 2021, read in the corpus; see
`docs/eternity-dependence-connection.md`): a thing persists through its earlier
existence and the absence of anything causing its cessation, with no concurrent
sustaining efficient cause. In `Control.inertia` every caused thing has an
originating cause, the contact principle holds, and nothing is sustained after
the originator ceases. That is a formal interpretation, not evidence about
reality.

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.SustainingCausation

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.GroundedBeginnings
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusImmenseIncomprehensible

/-- Explicitly identified PRIMITIVE relation (Encode first).

* `GivesAt v c x t` — in history `v`, `c` exercises causation of `x`'s being at
  moment `t`. The time index is the effect side: the moment at which the
  activity bears on `x`. Not counterfactual dependence, not removal of a
  destroyer, not `Ontic.Causes`.

No axiom constrains it. -/
structure BeingGiving (W B T : Type) where
  GivesAt : W → B → B → T → Prop

/-- CAUSE_OF_BEING_1, originating: `c` gives `x` being at a first moment of
`x`'s presence in history `v`. Requires such a first moment; nothing is
required of `c` at later moments. -/
def OriginatesBeing {W B T : Type} [Preorder T] (h : History W B T) (G : BeingGiving W B T)
    (v : W) (c x : B) : Prop :=
  ∃ b, BeginsAt h v x b ∧ G.GivesAt v c x b

/-- CAUSE_OF_BEING_2, sustaining: `x` is present at some moment of history `v`,
and `c` gives `x` being at every moment at which `x` is present. Types the
concurrence of the activity with the effect, not the dependence of the effect on
it. -/
def SustainsBeing {W B T : Type} (h : History W B T) (G : BeingGiving W B T)
    (v : W) (c x : B) : Prop :=
  (∃ t, h.IsAt v x t) ∧ ∀ t, h.IsAt v x t → G.GivesAt v c x t

/-- Contact principle, time-indexed (after ST I q.8 a.1): in every history,
whatever gives a thing being at a moment is present at that moment. -/
def GiverPresentWhenGiving {W B T : Type} (h : History W B T) (G : BeingGiving W B T) : Prop :=
  ∀ v c x t, G.GivesAt v c x t → h.IsAt v c t

/-- `g` is present, by giving being, to every other thing at every moment at
which that thing is present in history `v`: the typed presence of q.8 a.1 ("as
an agent is present to that upon which it works"). Not place, containment,
measure, presence by power or by knowledge, or immediacy. -/
def PresentToAllWheneverTheyAre {W B T : Type} (h : History W B T) (G : BeingGiving W B T)
    (v : W) (g : B) : Prop :=
  ∀ x t, x ≠ g → h.IsAt v x t → h.IsAt v g t ∧ G.GivesAt v g x t

/-- `g` sustains the being of every other thing present at some moment of
history `v`. -/
def SustainsAllOthers {W B T : Type} (h : History W B T) (G : BeingGiving W B T)
    (v : W) (g : B) : Prop :=
  ∀ x, x ≠ g → (∃ t, h.IsAt v x t) → SustainsBeing h G v g x

/-- In every history, whatever sustains every other thing is present to every
other thing whenever it is. -/
def SustainerOfAllIsPresentToAll {W B T : Type} (h : History W B T)
    (G : BeingGiving W B T) : Prop :=
  ∀ v g, SustainsAllOthers h G v g → PresentToAllWheneverTheyAre h G v g

/-- Sustaining reading of the tenseless cause of being (open bridge from
CAUSING_AN_EFFECT_3 to CAUSE_OF_BEING_2): in every history, a cause of `x`'s
being (`CausesIn c x esse`) gives `x` being at every moment at which `x` is
present. -/
def CausingBeingIsSustaining {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect) : Prop :=
  ∀ v c x, CausesIn c x esse → (∃ t, h.IsAt v x t) → SustainsBeing h G v c x

/-- Originating reading of the tenseless cause of being (the rival reading,
used in the controls): in every history, a cause of `x`'s being originates it. -/
def CausingBeingIsOriginating {W B T Respect : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect) : Prop :=
  ∀ v c x, CausesIn c x esse → (∃ t, h.IsAt v x t) → OriginatesBeing h G v c x

/-- Whatever is present at a moment of a history is in act as to being. The
history-level counterpart of the world-level `ExistenceActuality.ExistingInActAt`
(statement `0436de86`); neither is derived from the other. -/
def PresentIsInActAsToBeing {W B T Respect : Type} (h : History W B T)
    (InAct : B → Respect → Prop) (esse : Respect) : Prop :=
  ∀ v x t, h.IsAt v x t → InAct x esse

/-- Whatever is IMMENSE_2 is, in every history, present by giving being to every
other thing whenever it is. -/
def Immense2PresentToAll {W B T Respect : Type} (h : History W B T) (G : BeingGiving W B T)
    (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (Infinite : B → Prop) : Prop :=
  ∀ v g, IsImmenseAsInfiniteCauseOfAll InAct CausesIn esse Infinite g →
    PresentToAllWheneverTheyAre h G v g

/-- Narrowed sense bridge IMMENSE_2 → IMMENSE_1: whatever is IMMENSE_2 and, in
every history, present by giving being to every other thing whenever it is, is
IMMENSE_1. It carries what remains of `InfiniteCauseOfAllIsImmense` once the
presence step is typed: place, containment and measure; presence by power and by
knowledge; immediacy; and the passage from the typed presence to the primitive. -/
def PresentInfiniteCauseOfAllIsImmense {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop) (D : Primitives B) : Prop :=
  ∀ g, IsImmenseAsInfiniteCauseOfAll InAct CausesIn esse Infinite g →
    (∀ v, PresentToAllWheneverTheyAre h G v g) → D.Immense g

/-- In every history, a concrete thing absent at a moment and present at a
strictly later one has a concrete sustaining cause. -/
def BeginningsHaveSustainingCause {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : BeingGiving W B T) : Prop :=
  ∀ v x s t, Concrete x → s < t → ¬ h.IsAt v x s → h.IsAt v x t →
    ∃ g, Concrete g ∧ SustainsBeing h G v g x

/-- In every history, a concrete thing absent at a moment and present at a
strictly later one has a concrete originating cause. Requires a first moment of
its presence. -/
def BeginningsHaveOriginatingCause {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : BeingGiving W B T) : Prop :=
  ∀ v x s t, Concrete x → s < t → ¬ h.IsAt v x s → h.IsAt v x t →
    ∃ g, Concrete g ∧ OriginatesBeing h G v g x

/-- Every sustaining cause is a ground under the supplied grounding relation. -/
def SustainersAreGrounds {W B T : Type} (h : History W B T) (G : BeingGiving W B T)
    (grounds : W → B → B → Prop) : Prop :=
  ∀ v g x, SustainsBeing h G v g x → grounds v g x

/-- Every originating cause is a ground under the supplied grounding relation. -/
def OriginatorsAreGrounds {W B T : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (grounds : W → B → B → Prop) : Prop :=
  ∀ v g x, OriginatesBeing h G v g x → grounds v g x

/-- No return after absence: in every history, a concrete thing present at `a`
and at a later `t` is present at every moment between them. -/
def ConcretePresenceConvex {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) : Prop :=
  ∀ v x a s t, Concrete x → a < s → s < t → h.IsAt v x a → h.IsAt v x t → h.IsAt v x s

/-- Any two moments are comparable: one is strictly earlier, or they are the
same. Stated for the supplied preorder of times, as a premise rather than a
`LinearOrder` instance, so that a route using it covers every model in which it
holds and lists it among its open premises. -/
def TimesTrichotomous (T : Type) [Preorder T] : Prop :=
  ∀ a b : T, a < b ∨ a = b ∨ b < a

namespace Control

/-- One world, accessible from itself. -/
def unitFrame : TruthCore.Modal.Frame Unit := ⟨fun _ _ => True⟩

/-- Existential inertia: `true` (the cause) is present at times `0` and `1`,
`false` (the effect) at every time from `1` on; `true` gives `false` being at
time `1` only. -/
def inertia : History Unit Bool Nat where
  ontic := { frame := unitFrame, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  IsAt := fun _ b t => (b = true ∧ t ≤ 1) ∨ (b = false ∧ 1 ≤ t)
  now := 1

/-- Giving at time `1` only, from `true` to `false`. -/
def inertiaGiving : BeingGiving Unit Bool Nat := ⟨fun _ c x t => c = true ∧ x = false ∧ t = 1⟩

/-- An absent giver: `false` is present from time `1` on; `true` is never
present. -/
def absentGiver : History Unit Bool Nat where
  ontic := { frame := unitFrame, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  IsAt := fun _ b t => b = false ∧ 1 ≤ t
  now := 1

/-- `true` gives `false` being at every time. -/
def alwaysGiving : BeingGiving Unit Bool Nat := ⟨fun _ c x _ => c = true ∧ x = false⟩

/-- Sustained: `true` is present at every time, `false` from time `1` on. -/
def sustained : History Unit Bool Nat where
  ontic := { frame := unitFrame, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  IsAt := fun _ b t => b = true ∨ (b = false ∧ 1 ≤ t)
  now := 1

/-- `true` gives `false` being at every time from `1` on. -/
def sustainedGiving : BeingGiving Unit Bool Nat := ⟨fun _ c x t => c = true ∧ x = false ∧ 1 ≤ t⟩

/-- No giving. -/
def noGiving : BeingGiving Unit Bool Nat := ⟨fun _ _ _ _ => False⟩

/-- Intermittent presence: `true` is present at time `0` only, `false` at times
`0` and `2`. -/
def intermittent : History Unit Bool Nat where
  ontic := { frame := unitFrame, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  IsAt := fun _ b t => (b = true ∧ t = 0) ∨ (b = false ∧ (t = 0 ∨ t = 2))
  now := 2

/-- `true` gives `false` being at time `0` only. -/
def intermittentGiving : BeingGiving Unit Bool Nat := ⟨fun _ c x t => c = true ∧ x = false ∧ t = 0⟩

/-- `true` causes the being of `false`. -/
def trueCausesFalse : Bool → Bool → Unit → Prop := fun c x _ => c = true ∧ x = false

/-- No cause of being. -/
def noCauses : Bool → Bool → Unit → Prop := fun _ _ _ => False

/-- `true` grounds `false`. -/
def trueGroundsFalse : Unit → Bool → Bool → Prop := fun _ c x => c = true ∧ x = false

/-- No grounds. -/
def noGroundsU : Unit → Bool → Bool → Prop := fun _ _ _ => False

/-- Everything is in act as to being. -/
def everything : Bool → Unit → Prop := fun _ _ => True

/-- Nothing is in act. -/
def nothing : Bool → Unit → Prop := fun _ _ => False

/-- Everything counts as concrete. -/
def allB : Bool → Prop := fun _ => True

/-- Only `true` is infinite. -/
def isTrue : Bool → Prop := fun b => b = true

/-- Omission, rival-reading and nonvacuity controls, every individual concrete.
(1) `inertia` (existential inertia): the originating reading, presence-in-act and
the contact principle hold and `true` is IMMENSE_2, but the sustaining reading
fails and `true` is not present to all whenever they are; the originating route
to the lasting-ground premise A2ab holds in full with A2ab, while the
sustaining-cause premise fails. (2) `absentGiver`: without the contact principle,
the sustaining reading and presence-in-act hold and presence to all fails; the
sustaining-cause and sustainers-are-grounds premises hold and A2ab fails.
(3) `sustained` with no giving: without the sustaining reading, presence-in-act
and the contact principle hold and presence to all fails; with no grounds,
sustainers-are-grounds and the contact principle hold, the sustaining-cause
premise fails and A2ab fails. (4) `sustained` with nothing in act: the sustaining
reading and the contact principle hold, `true` is IMMENSE_2 (vacuously creator)
and presence to all fails. (5) `sustained` with no grounds: the sustaining-cause
premise and the contact principle hold and A2ab fails. (6) `intermittent`: the
originating-cause, originators-are-grounds, contact and trichotomy premises hold,
convexity fails and A2ab fails. (7) `sustained` with its giving: every premise of
both routes holds (trichotomy included), `true` is IMMENSE_2 and present to all, and A2ab holds. -/
def Certificate : Prop :=
  (CausingBeingIsOriginating inertia inertiaGiving trueCausesFalse () ∧
    ¬ CausingBeingIsSustaining inertia inertiaGiving trueCausesFalse () ∧
    PresentIsInActAsToBeing inertia everything () ∧
    GiverPresentWhenGiving inertia inertiaGiving ∧
    IsImmenseAsInfiniteCauseOfAll everything trueCausesFalse () isTrue true ∧
    ¬ Immense2PresentToAll inertia inertiaGiving everything trueCausesFalse () isTrue ∧
    BeginningsHaveOriginatingCause inertia allB inertiaGiving ∧
    OriginatorsAreGrounds inertia inertiaGiving trueGroundsFalse ∧
    ConcretePresenceConvex inertia allB ∧
    BeginningsHaveLastingGround inertia allB trueGroundsFalse ∧
    ¬ BeginningsHaveSustainingCause inertia allB inertiaGiving) ∧
  (CausingBeingIsSustaining absentGiver alwaysGiving trueCausesFalse () ∧
    PresentIsInActAsToBeing absentGiver everything () ∧
    ¬ GiverPresentWhenGiving absentGiver alwaysGiving ∧
    ¬ Immense2PresentToAll absentGiver alwaysGiving everything trueCausesFalse () isTrue ∧
    BeginningsHaveSustainingCause absentGiver allB alwaysGiving ∧
    SustainersAreGrounds absentGiver alwaysGiving trueGroundsFalse ∧
    ¬ BeginningsHaveLastingGround absentGiver allB trueGroundsFalse) ∧
  (¬ CausingBeingIsSustaining sustained noGiving trueCausesFalse () ∧
    PresentIsInActAsToBeing sustained everything () ∧
    GiverPresentWhenGiving sustained noGiving ∧
    ¬ Immense2PresentToAll sustained noGiving everything trueCausesFalse () isTrue ∧
    SustainersAreGrounds sustained noGiving noGroundsU ∧
    ¬ BeginningsHaveSustainingCause sustained allB noGiving ∧
    ¬ BeginningsHaveLastingGround sustained allB noGroundsU) ∧
  (CausingBeingIsSustaining sustained noGiving noCauses () ∧
    ¬ PresentIsInActAsToBeing sustained nothing () ∧
    GiverPresentWhenGiving sustained noGiving ∧
    IsImmenseAsInfiniteCauseOfAll nothing noCauses () isTrue true ∧
    ¬ Immense2PresentToAll sustained noGiving nothing noCauses () isTrue) ∧
  (BeginningsHaveSustainingCause sustained allB sustainedGiving ∧
    GiverPresentWhenGiving sustained sustainedGiving ∧
    ¬ SustainersAreGrounds sustained sustainedGiving noGroundsU ∧
    ¬ BeginningsHaveLastingGround sustained allB noGroundsU) ∧
  (BeginningsHaveOriginatingCause intermittent allB intermittentGiving ∧
    OriginatorsAreGrounds intermittent intermittentGiving trueGroundsFalse ∧
    GiverPresentWhenGiving intermittent intermittentGiving ∧
    TimesTrichotomous Nat ∧
    ¬ ConcretePresenceConvex intermittent allB ∧
    ¬ BeginningsHaveLastingGround intermittent allB trueGroundsFalse) ∧
  (CausingBeingIsSustaining sustained sustainedGiving trueCausesFalse () ∧
    PresentIsInActAsToBeing sustained everything () ∧
    GiverPresentWhenGiving sustained sustainedGiving ∧
    IsImmenseAsInfiniteCauseOfAll everything trueCausesFalse () isTrue true ∧
    Immense2PresentToAll sustained sustainedGiving everything trueCausesFalse () isTrue ∧
    BeginningsHaveSustainingCause sustained allB sustainedGiving ∧
    SustainersAreGrounds sustained sustainedGiving trueGroundsFalse ∧
    BeginningsHaveOriginatingCause sustained allB sustainedGiving ∧
    OriginatorsAreGrounds sustained sustainedGiving trueGroundsFalse ∧
    ConcretePresenceConvex sustained allB ∧
    TimesTrichotomous Nat ∧
    BeginningsHaveLastingGround sustained allB trueGroundsFalse)

end Control

end TruthCore.Causality.SustainingCausation
