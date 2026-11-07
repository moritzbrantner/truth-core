module

public import TruthCore.Logic.CogitoConcrete
public import TruthCore.Logic.PerformedDenial
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Causality.SelectedAncestry
public import TruthCore.Causality.ConcreteExistentialSupply
public import TruthCore.Greek.Aristotle.MetaphysicsIX
public import TruthCore.Greek.Aristotle.Physics

/-!
Round 3 of the exploration maps for the Cogito/existence base and the
Aristotelian analyses (`explorations/cogito-thought-occurs.toml` and siblings).
Analyst formulations, attribution deferred: every new definition below is an
OPEN premise, not a source reading and not a Lean fact.

* **Cogito by retorsion.** A performed doubt (or denial) whether any thought
  occurs is itself realized by an occurring thought episode. From that premise
  alone, the doubted content "no thought episode occurs" is false whenever the
  doubt is performed; with the further premise that such a doubt is performed,
  some thought episode occurs. `Act` (performed acts) and `Episode` (thought
  episodes) are separate carriers joined by `Realizes`, so the step from a
  performed act to an occurring episode is an explicit premise.
* **Opining.** Every occurring thought episode is an assenting episode, and the
  bearer of an assenting episode opines its content. A willing or a doubting
  that is no assent falsifies the first premise.
* **Selected bearer.** The selected being bears an occurring thought episode;
  with the existing bearer bridges it is an actual concretum.
* **Finite grounding rank.** Actual concrete grounding descends along a
  natural-number rank. This is STRONGER than well-foundedness (a Nat rank
  excludes transfinite grounding heights, compare `CommonRank`); it gives
  well-founded actual grounding without excluded middle and, with excluded
  middle, the no-self-contained-borrowing cut.
* **No contingent root ancestor.** The selected cone has no contingent root;
  with excluded middle every contingent cone member has an actual concrete
  ground.
* **Potency through privation.** Potency is capacity under privation, and
  privation in a capable subject is the lack of the act.
* **Motion as actualization of an unactualized capacity.** Being moved in `r`
  is the actualization, qua potential, of an unactualized capacity for `r`.
-/

@[expose] public section

namespace TruthCore.Causality.Round3CogitoBase

open TruthCore.Logic.PerformedDenial (NoEpisodeOccurs)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.SelectedAncestry (ContingentRootAncestor)

/-! ## Cogito by retorsion -/

/-- OPEN: some doubt (or denial) whether any thought episode occurs is
actually performed. `DoubtsThought a` says only that `a` is a doubting or
denying of thought occurrence; `Performed a` that it is actually carried out.
The premise is the inquirer's own present act, not a general principle. -/
def DoubtIsPerformed {Act : Type} (Performed DoubtsThought : Act → Prop) : Prop :=
  ∃ a, Performed a ∧ DoubtsThought a

/-- OPEN analyst bridge (doubting is a mode of thinking): every performed doubt
whether thought occurs is realized by some occurring thought episode. -/
def PerformedDoubtIsThought {Act Episode : Type} (Performed DoubtsThought : Act → Prop)
    (Occurs : Episode → Prop) (Realizes : Act → Episode → Prop) : Prop :=
  ∀ a, Performed a → DoubtsThought a → ∃ e, Occurs e ∧ Realizes a e

/-- Retorsion: whoever actually performs a doubt or denial that any thought
occurs makes the doubted content, "no thought episode occurs", false. It says
nothing about an unperformed doubt (compare `EmptyEpisodeControl`). -/
def PerformedDoubtOfThoughtSelfRefuting {Act Episode : Type}
    (Performed DoubtsThought : Act → Prop) (Occurs : Episode → Prop) : Prop :=
  ∀ a, Performed a → DoubtsThought a → ¬ NoEpisodeOccurs Occurs

/-! ## Opining -/

/-- OPEN: every occurring thought episode is an assenting episode (it takes its
content to be so). A willing, or a doubt without assent, falsifies it. -/
def OccurringThoughtIsAssenting {Episode : Type} (Occurs Assenting : Episode → Prop) : Prop :=
  ∀ e, Occurs e → Assenting e

/-- OPEN: the bearer of an assenting episode opines that episode's content
(`DEF-OPINING`). -/
def AssentingBearerOpinesContent {E Episode : Type} (Bears : E → Episode → Prop)
    (Assenting : Episode → Prop) (Opines : E → Prop → Prop) (content : Episode → Prop) : Prop :=
  ∀ b e, Bears b e → Assenting e → Opines b (content e)

/-! ## Selected bearer -/

/-- OPEN: the selected being bears some occurring thought episode. -/
def SelectedBearsOccurringThought {B Episode : Type} (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (selected : B) : Prop :=
  ∃ e, Occurs e ∧ Bears selected e

/-! ## Grounding -/

/-- OPEN: actual concrete grounding at `w` descends along a natural-number
rank: whenever an actual concretum `y` grounds an actual concretum `x`, `y` has
a smaller rank. Strictly stronger than `ActualGroundingWF`: a Nat rank excludes
grounding chains of transfinite height, which well-foundedness allows. -/
def ActualGroundingFiniteRank {W B : Type} (m : Profile W B) (w : W) : Prop :=
  ∃ rank : B → Nat, ∀ x y, ActualConcrete m w x → ActualConcrete m w y →
    m.grounds w y x → rank y < rank x

/-- OPEN: the selected being's actual grounding cone has no contingent root
ancestor (no contingent cone member without an actual concrete ground). -/
def NoContingentRootAncestor {W B : Type} (m : Profile W B) (w : W) (selected : B) : Prop :=
  ¬ ContingentRootAncestor m w selected

/-! ## Act and potency -/

/-- OPEN: to be in potency to `r` is to be capable of `r` and deprived of it
(the subject-privation pair of *Physics* I.7 applied to capacities). -/
def PotencyIsCapacityUnderPrivation {Being Respect : Type}
    (InPotency CanBe Deprived : Being → Respect → Prop) : Prop :=
  ∀ x r, InPotency x r ↔ CanBe x r ∧ Deprived x r

/-- OPEN: in a subject capable of `r`, privation of `r` is exactly the lack of
`r` in act. -/
def PrivationIsLackOfActInCapable {Being Respect : Type}
    (InAct CanBe Deprived : Being → Respect → Prop) : Prop :=
  ∀ x r, CanBe x r → (Deprived x r ↔ ¬ InAct x r)

/-- OPEN: being moved in `r` is the actualization, qua potential, of an
unactualized capacity for `r`: a capacity for `r` not yet `r` in act. -/
def BeingMovedIsActualizationOfUnactualizedCapacity {Being Respect : Type}
    (MovedIn InAct CanBe ActualizedQuaPotential : Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r ↔ (CanBe x r ∧ ¬ InAct x r) ∧ ActualizedQuaPotential x r

/-! ## Controls

Hand-written omission models (one per load-bearing premise) and one joint
nonvacuity witness per vocabulary. Excluded middle is never a conjunct of a
model: it holds in every classical model but is not provable without an axiom,
so no omission model of excluded middle exists and the models for the
excluded-middle edges state only the remaining premises. Satisfiability and
omission only; no model is claimed to describe reality. -/

namespace Control

open TruthCore.Logic.CogitoSubject (ThoughtOccurs)
open TruthCore.Logic.CogitoConcrete (EveryBearerIsConcrete EveryBearerExistsAt
  BorneThoughtIsOpining unitOntic)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Causality.SelectedAncestry (ConeWellFounded ConeContingentGrounded)
open TruthCore.Causality.ConcreteExistentialSupply (ActualConcreteBorrowingEscape)
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

/-- Constant predicates over `Unit`. -/
abbrev on (p : Prop) : Unit → Prop := fun _ => p
abbrev on2 (p : Prop) : Unit → Unit → Prop := fun _ _ => p

/-- A one-candidate profile over `Unit`: existence `ex`, concreteness `c`,
grounding `g` (a self-loop when `g` is true). -/
def unitProfile (ex c g : Prop) : Profile Unit Unit where
  ontic := unitOntic ex
  concrete := fun _ => c
  grounds := fun _ _ _ => g

/-- Two worlds and two candidates. `false` exists at every world, `true` only
at world `true`; every world sees every world; both are concrete; `false`
grounds `true` and nothing else is grounded. -/
def rootedProfile : Profile Bool Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w b => b = false ∨ w = true
    Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding/modal structure, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := fun _ y x => y = false ∧ x = true

/-- `true` exists only at world `true`, with no ground: a contingent root. -/
def contingentRootProfile : Profile Bool Unit where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w _ => w = true
    Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding/modal structure, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := fun _ _ _ => False

/-- `doubtIsPerformed` and `performedDoubtSelfRefuting` without
`PerformedDoubtIsThought`: a performed doubt with no occurring episode. -/
def DoubtWithoutThought : Prop :=
  DoubtIsPerformed (on True) (on True) ∧
  ¬ PerformedDoubtIsThought (on True) (on True) (on False) (on2 True) ∧
  ¬ ThoughtOccurs (on False) ∧
  ¬ PerformedDoubtOfThoughtSelfRefuting (on True) (on True) (on False)

/-- `thoughtOccursFromPerformedDoubt` without `DoubtIsPerformed`: nothing is
performed, the bridge holds vacuously, no thought occurs. -/
def NoPerformedDoubt : Prop :=
  ¬ DoubtIsPerformed (on False) (on True) ∧
  PerformedDoubtIsThought (on False) (on True) (on False) (on2 True) ∧
  ¬ ThoughtOccurs (on False)

/-- Without `OccurringThoughtIsAssenting`: an occurring borne episode that is
no assent (a willing); nobody opines anything. -/
def NonAssentingThought : Prop :=
  ¬ OccurringThoughtIsAssenting (on True) (on False) ∧
  AssentingBearerOpinesContent (on2 True) (on False) (fun _ _ => False) (on True) ∧
  ¬ BorneThoughtIsOpining (on True) (on2 True) (fun _ _ => False) (on True)

/-- Without `AssentingBearerOpinesContent`: an assenting episode whose bearer
opines nothing. -/
def AssentWithoutOpining : Prop :=
  OccurringThoughtIsAssenting (on True) (on True) ∧
  ¬ AssentingBearerOpinesContent (on2 True) (on True) (fun _ _ => False) (on True) ∧
  ¬ BorneThoughtIsOpining (on True) (on2 True) (fun _ _ => False) (on True)

/-- Without `SelectedBearsOccurringThought`: no thought occurs, the selected
candidate is not concrete. -/
def SelectedBearsNothing : Prop :=
  let m := unitProfile True False False
  ¬ SelectedBearsOccurringThought (on False) (on2 True) () ∧
  EveryBearerIsConcrete (on False) (on2 True) m.concrete ∧
  EveryBearerExistsAt m.ontic (on False) (on2 True) () ∧
  ¬ ActualConcrete m () ()

/-- Without `EveryBearerIsConcrete`: the selected bearer exists but is not
concrete. -/
def AbstractSelectedBearer : Prop :=
  let m := unitProfile True False False
  SelectedBearsOccurringThought (on True) (on2 True) () ∧
  ¬ EveryBearerIsConcrete (on True) (on2 True) m.concrete ∧
  EveryBearerExistsAt m.ontic (on True) (on2 True) () ∧
  ¬ ActualConcrete m () ()

/-- Without `EveryBearerExistsAt`: the selected bearer is concrete but does
not exist at the world. -/
def AbsentSelectedBearer : Prop :=
  let m := unitProfile False True False
  SelectedBearsOccurringThought (on True) (on2 True) () ∧
  EveryBearerIsConcrete (on True) (on2 True) m.concrete ∧
  ¬ EveryBearerExistsAt m.ontic (on True) (on2 True) () ∧
  ¬ ActualConcrete m () ()

/-- Without the finite rank (and without the global well-foundedness for the
cone edge): one actual concretum grounds itself. No rank, no well-founded
actual grounding, no well-founded cone, and the borrowing cut fails. -/
def SelfGroundingLoop : Prop :=
  let m := unitProfile True True True
  ¬ ActualGroundingFiniteRank m () ∧ ¬ ActualGroundingWF m () ∧
  ¬ ConeWellFounded m () () ∧ ¬ ActualConcreteBorrowingEscape m ()

/-- Without `NoContingentRootAncestor`: the selected being is a contingent
root, so a contingent cone member lacks an actual concrete ground. -/
def ContingentRootCone : Prop :=
  ¬ NoContingentRootAncestor contingentRootProfile true () ∧
  ¬ ConeContingentGrounded contingentRootProfile true ()

/-- Without `PotencyIsCapacityUnderPrivation`: a capable, deprived subject
that is not in potency. -/
def CapacityWithoutPotency : Prop :=
  ¬ PotencyIsCapacityUnderPrivation (on2 False) (on2 True) (on2 True) ∧
  PrivationIsLackOfActInCapable (on2 False) (on2 True) (on2 True) ∧
  ¬ PotencyIsUnactualizedCapacityReading (on2 False) (on2 False) (on2 True)

/-- Without `PrivationIsLackOfActInCapable`: a privation that coexists with
the act. -/
def PrivationWithAct : Prop :=
  PotencyIsCapacityUnderPrivation (on2 True) (on2 True) (on2 True) ∧
  ¬ PrivationIsLackOfActInCapable (on2 True) (on2 True) (on2 True) ∧
  ¬ PotencyIsUnactualizedCapacityReading (on2 True) (on2 True) (on2 True)

/-- Without `BeingMovedIsActualizationOfUnactualizedCapacity`: a moved thing
with no capacity, potency or actualization. -/
def MotionWithoutCapacity : Prop :=
  ¬ BeingMovedIsActualizationOfUnactualizedCapacity (on2 True) (on2 False) (on2 False) (on2 False) ∧
  PotencyIsUnactualizedCapacityReading (on2 False) (on2 False) (on2 False) ∧
  ¬ BeingMovedIsActualizationOfPotencyReading (on2 True) (on2 False) (on2 False)

/-- Without `PotencyIsUnactualizedCapacityReading`: an unactualized capacity
that is not counted as potency. -/
def CapacityNotPotency : Prop :=
  BeingMovedIsActualizationOfUnactualizedCapacity (on2 True) (on2 False) (on2 True) (on2 True) ∧
  ¬ PotencyIsUnactualizedCapacityReading (on2 False) (on2 False) (on2 True) ∧
  ¬ BeingMovedIsActualizationOfPotencyReading (on2 True) (on2 False) (on2 True)

/-- Joint nonvacuity witness for the Cogito, opining and selected-bearer edges:
one performed doubt realized by one occurring assenting episode, borne by one
actual concrete candidate that opines its content. Every premise and
conclusion holds. -/
def CogitoWitness : Prop :=
  let m := unitProfile True True False
  DoubtIsPerformed (on True) (on True) ∧
  PerformedDoubtIsThought (on True) (on True) (on True) (on2 True) ∧
  ThoughtOccurs (on True) ∧
  PerformedDoubtOfThoughtSelfRefuting (on True) (on True) (on True) ∧
  OccurringThoughtIsAssenting (on True) (on True) ∧
  AssentingBearerOpinesContent (on2 True) (on True) (fun _ _ => True) (on True) ∧
  BorneThoughtIsOpining (on True) (on2 True) (fun _ _ => True) (on True) ∧
  SelectedBearsOccurringThought (on True) (on2 True) () ∧
  EveryBearerIsConcrete (on True) (on2 True) m.concrete ∧
  EveryBearerExistsAt m.ontic (on True) (on2 True) () ∧
  ActualConcrete m () ()

/-- Joint nonvacuity witness for the grounding edges (excluded middle aside):
a necessary root `false` grounding a contingent `true`. The finite rank, global
and cone well-foundedness, no contingent root ancestor and cone contingent
grounding all hold at world `true` for the selected `true`, with a real
grounding edge. -/
def GroundingWitness : Prop :=
  ActualGroundingFiniteRank rootedProfile true ∧
  ActualGroundingWF rootedProfile true ∧
  ConeWellFounded rootedProfile true true ∧
  NoContingentRootAncestor rootedProfile true true ∧
  ConeContingentGrounded rootedProfile true true ∧
  rootedProfile.grounds true false true

/-- Joint nonvacuity witness for the act/potency edges: a capable, deprived,
potent subject being moved. -/
def PotencyWitness : Prop :=
  PotencyIsCapacityUnderPrivation (on2 True) (on2 True) (on2 True) ∧
  PrivationIsLackOfActInCapable (on2 False) (on2 True) (on2 True) ∧
  PotencyIsUnactualizedCapacityReading (on2 False) (on2 True) (on2 True) ∧
  BeingMovedIsActualizationOfUnactualizedCapacity (on2 True) (on2 False) (on2 True) (on2 True) ∧
  BeingMovedIsActualizationOfPotencyReading (on2 True) (on2 True) (on2 True)

/-- All controls of the batch. -/
def Certificate : Prop :=
  DoubtWithoutThought ∧ NoPerformedDoubt ∧ NonAssentingThought ∧ AssentWithoutOpining ∧
  SelectedBearsNothing ∧ AbstractSelectedBearer ∧ AbsentSelectedBearer ∧
  SelfGroundingLoop ∧ ContingentRootCone ∧
  CapacityWithoutPotency ∧ PrivationWithAct ∧ MotionWithoutCapacity ∧ CapacityNotPotency ∧
  CogitoWitness ∧ GroundingWitness ∧ PotencyWitness

end Control

end TruthCore.Causality.Round3CogitoBase
