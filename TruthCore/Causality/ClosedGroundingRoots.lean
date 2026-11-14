module

public import TruthCore.Causality.GradedSupportFoundation
public import TruthCore.Causality.NecessarySupportActualScope
public import TruthCore.Causality.NecessaryConcreteRouteBridge
public import TruthCore.Causality.QuantitativeTransferPaths

/-!
# Closed grounding collections have a root: the regress demand of the join

Analyst formulations, attribution deferred (#310). Target: the weakest
no-infinite-regress commitment that the stage-one join of the modal spine
(`STMT-NECESSARY-CONCRETE-UNDERIVED-AT`) actually consumes.

Every join route that uses well-founded actual grounding
(`NecessaryRootFork.ActualGroundingWF`, AGWF) uses it only to find an actual
root: by well-founded induction, an actual concretum, or a necessary one, has an
actual root among (or as) its ancestors. Well-foundedness says more: it also
excludes infinite descending chains and cycles that sit *above* a root.
`ClosedGroundingCollectionsRooted` states only what the routes use:

* a collection `S` of actual concreta is **ground-closed** at `w` when it contains
  every actual concrete ground of each of its members (`GroundClosedActual`);
* no ground-closed collection is both nonempty and without an actual root. In
  words: a collection of actual concreta that contains every actual ground of each
  of its members, so that each member's being is supplied only from inside the
  collection, contains a member whose being is not supplied by any actual concretum.

Its closure is over actual *concrete* grounds only: an actual root may have an
abstract or unmodelled ground. The borrowed-reality principle over all modelled
suppliers (`NoWhollyBorrowedCollection`) gives it only with the bridge that actual
concreta are supplied only by concreta (`ActualSuppliersOfConcretaConcrete`;
`closedRootedOfBorrowed`, and `Control.abstractSupplier` without the bridge). It is the condition of well-foundedness (every nonempty collection has a
minimal element) restricted to ground-closed collections. AGWF implies it
constructively (`closedRootedOfWF`); it does not imply AGWF (`Control.limitGrounder`:
one root directly grounds every member of an infinite descending chain), nor grounding
asymmetry (`Control.rootedCycle`).

`AttenuatedEsseReception` is the quantitative per se bridge: every actual concretum
has a positive, commonly bounded amount of esse; its esse is at most its own
(unreceived) esse plus the weighted esse it receives along actual grounding, with a
uniform loss (total incoming weight at most `q < 1`); and only a thing with no actual
concrete ground has esse of its own (intermediates contribute nothing of their own).
Composed with the existing weighted-network theorem
`QuantitativeTransferPaths.finitePath`, it gives the closed-collection condition.
The network analogues in that batch (`binaryFixed`, `halfFixed`) show that the
weighted-network theorem fails without uniform loss or without the common bound;
no Profile-level control is given here.

No premise here is established; the selected relation is not identified with
efficient causing (`DEF-PRESENT-ESSE-SUPPORT`).
-/

@[expose] public section

namespace TruthCore.Causality.ClosedGroundingRoots

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportActualScope
open TruthCore.Causality.NecessaryConcreteRouteBridge (ActualGroundingAsymmetric)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive NoNovelNecessarySupport)
open TruthCore.Causality.GradedSupportFoundation (NoInfiniteAscentAmongActualConcreta)
open TruthCore.Causality.SpineRivalsRootEsse (NecessaryConcretaMutualSupport)
open TruthCore.Causality.Round2Grounding (ActualGroundIsMoreInEsse)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B : Type}

/-- `S` is a collection of actual concreta at `w` that contains every actual
concrete ground at `w` of each of its members. -/
def GroundClosedActual (m : Profile W B) (w : W) (S : B → Prop) : Prop :=
  (∀ x, S x → ActualConcrete m w x) ∧
    ∀ x y, S x → ActualConcreteGround m w y x → S y

/-- No collection of actual concreta at `w` that is closed under actual concrete
grounds is both nonempty and without an actual root: if every member of such a
collection has an actual concrete ground, the collection is empty. Constrains
only ground-closed collections; an infinite descending chain or a cycle of grounds
is allowed when a root grounds into it. -/
def ClosedGroundingCollectionsRooted (m : Profile W B) (w : W) : Prop :=
  ∀ S : B → Prop, GroundClosedActual m w S → (∀ x, S x → ¬ ActualRoot m w x) →
    ∀ x, ¬ S x

/-- `S` is a collection of actual concreta at `w` that contains every candidate
existing at `w` that grounds a member at `w`, concrete or not: closure under all
modelled actual suppliers, not only concrete ones. -/
def SupplyClosedActual (m : Profile W B) (w : W) (S : B → Prop) : Prop :=
  (∀ x, S x → ActualConcrete m w x) ∧
    ∀ x y, S x → m.ontic.ExistsAt w y → m.grounds w y x → S y

/-- The borrowed-reality principle in its collection form, over every modelled
actual supplier: no collection of actual concreta that contains every actual
supplier of each member, concrete or not, is nonempty while each member has some
actual supplier. Suppliers outside the profile's selected relation are not
modelled. -/
def NoWhollyBorrowedCollection (m : Profile W B) (w : W) : Prop :=
  ∀ S : B → Prop, SupplyClosedActual m w S →
    (∀ x, S x → ¬ ∀ y, ¬ (m.ontic.ExistsAt w y ∧ m.grounds w y x)) → ∀ x, ¬ S x

/-- Every candidate existing at `w` that grounds an actual concretum at `w` is
concrete: the being of actual concreta is supplied, within the selected relation,
only by concreta. -/
def ActualSuppliersOfConcretaConcrete (m : Profile W B) (w : W) : Prop :=
  ∀ x y, ActualConcrete m w x → m.ontic.ExistsAt w y → m.grounds w y x → m.concrete y

/-- Per se reception of esse with uniform loss, on the actual concreta at `w`:
the actual concreta are countable; each has an amount `P` of esse, positive and at
most a common bound `M`; it receives weight `wt v u ≥ 0` only from an actual
concrete ground `u` of `v`, with total incoming weight at most `q < 1`; its esse is
at most its own esse `s v ≥ 0` plus the weighted esse it receives; and only an
actual root has positive own esse. The quantities are analyst parameters with no
real-world calibration. -/
def AttenuatedEsseReception (m : Profile W B) (w : W) : Prop :=
  Countable {x // ActualConcrete m w x} ∧
  ∃ (wt : {x // ActualConcrete m w x} → {x // ActualConcrete m w x} → ℝ)
    (s P : {x // ActualConcrete m w x} → ℝ) (q M : ℝ),
    0 ≤ q ∧ q < 1 ∧ 0 ≤ M ∧ (∀ v u, 0 ≤ wt v u) ∧ (∀ v, 0 ≤ s v) ∧
    (∀ v, P v ≤ M) ∧ (∀ v, Summable (wt v)) ∧ (∀ v, ∑' u, wt v u ≤ q) ∧
    (∀ v, Summable fun u => wt v u * P u) ∧
    (∀ v, P v ≤ s v + ∑' u, wt v u * P u) ∧
    (∀ v u, 0 < wt v u → m.grounds w u.1 v.1) ∧
    (∀ u, 0 < s u → ∀ y, ¬ ActualConcreteGround m w y u.1) ∧
    (∀ v, 0 < P v)

namespace Control

/-- A direct root grounder (named `limitGrounder`): one world; candidates `none`
(the root) and `some n`; `some (n+1)` grounds `some n`, and `none` DIRECTLY grounds
every `some n`. The descending chain never reaches the root by its own steps, but
the root directly grounds every member. A foundation reached only through
intermediaries is a different model (`mediateFoundation`). -/
def limitGrounder : Profile Unit (Option Nat) where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding structure, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := fun _ a b => (a = none ∧ b ≠ none) ∨ ∃ n, a = some (n+1) ∧ b = some n

/-- The grade of the limit grounder: the root is above every `some n`, and
`some n` is above `some k` when `k < n`. A maximum with unbounded ascent below it. -/
def limitGrade (_ : Unit) (a b : Option Nat) : Prop :=
  (a = none ∧ b ≠ none) ∨ ∃ n k, a = some n ∧ b = some k ∧ k < n

/-- Pure regress: one world, candidates `Nat`, `n+1` grounds `n`. Every actual
concretum has an actual concrete ground; there is no root anywhere. -/
def pureRegress : Profile Unit Nat where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding structure, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := fun _ a b => a = b + 1

/-- The ascending grade of the pure regress: `a` is above `b` when `b < a`. -/
def regressGrade (_ : Unit) (a b : Nat) : Prop := b < a

/-- A rooted cycle: one world; `none` grounds `some false` and `some true`,
which also ground each other. -/
def rootedCycle : Profile Unit (Option Bool) where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding structure, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := fun _ a b => (a = none ∧ b ≠ none) ∨ (a = some false ∧ b = some true) ∨
    (a = some true ∧ b = some false)

/-- The limit grounder satisfies the closed-collection condition, the premises of
the coverage routes of the join and the join's endpoint, and actual grounding
ascends a grade with a maximum; but actual grounding is not well-founded, the
grade has infinite ascent among actual concreta, and J2 fails although reflexive
access and the one-way no-novel-edge condition hold (so the closed-collection
condition cannot replace AGWF in J2's derivation). -/
def LimitGrounderControl : Prop :=
  ClosedGroundingCollectionsRooted limitGrounder () ∧
  ¬ ActualGroundingWF limitGrounder () ∧
  InhabitedConcreteAt limitGrounder.ontic limitGrounder.concrete () ∧
  EveryContingentGroundedAt limitGrounder () ∧
  ActualReflexive limitGrounder.ontic () ∧
  NoContingentConcreteSupport limitGrounder () ∧
  ActualNoContingentConcreteSupport limitGrounder () ∧
  NecessarySupportActuallyCovered limitGrounder () ∧
  NoNovelNecessarySupport (concreteOntic limitGrounder) (concreteSupport limitGrounder) () ∧
  ¬ ConcreteNecessaryUnionWF limitGrounder () ∧
  NecessaryConcreteUnderivedAt limitGrounder () ∧
  ActualGroundIsMoreInEsse limitGrounder () limitGrade () ∧
  (∀ y, ¬ limitGrade () y none) ∧
  ¬ NoInfiniteAscentAmongActualConcreta limitGrounder () limitGrade ()

/-- In the pure regress the closed-collection condition fails while every other
premise of the two from-necessity coverage routes holds (a necessary concretum,
J1, its actual-world instance and coverage), and every actual contingent concretum
is grounded; actual grounding ascends a grade; the join's endpoint fails. -/
def PureRegressControl : Prop :=
  ¬ ClosedGroundingCollectionsRooted pureRegress () ∧
  NecessaryConcreteAt pureRegress () ∧
  EveryContingentGroundedAt pureRegress () ∧
  NoContingentConcreteSupport pureRegress () ∧
  ActualNoContingentConcreteSupport pureRegress () ∧
  NecessarySupportActuallyCovered pureRegress () ∧
  ActualGroundIsMoreInEsse pureRegress () regressGrade () ∧
  ¬ NecessaryConcreteUnderivedAt pureRegress ()

/-- In the rooted cycle the closed-collection condition holds, with reflexive
access and the one-way no-novel-edge condition, while actual grounding is neither
asymmetric nor well-founded and two necessary concreta support each other. -/
def RootedCycleControl : Prop :=
  ClosedGroundingCollectionsRooted rootedCycle () ∧
  ActualReflexive rootedCycle.ontic () ∧
  NoNovelNecessarySupport (concreteOntic rootedCycle) (concreteSupport rootedCycle) () ∧
  ¬ ActualGroundingAsymmetric rootedCycle () ∧
  ¬ ActualGroundingWF rootedCycle () ∧
  NecessaryConcretaMutualSupport rootedCycle ()

/-- A one-point profile with no grounding: the per se attenuation bridge holds
(with own esse one, no reception) together with the closed-collection condition. -/
def point : Profile Unit Unit where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests the quantitative bridge's satisfiability only)
  grounds := fun _ _ _ => False

/-- The attenuation bridge is satisfiable (a minimal, edgeless witness). -/
def AttenuationSatisfiable : Prop := AttenuatedEsseReception point ()

/-- Foundation through intermediaries only, under direct grounding: `some (n+1)`
directly grounds `some n`, and the root `none` directly grounds nothing. Read
with a mediate (transitive) relation, `none` would be a limit ground of the chain;
the selected relation is direct support, so the chain is a rootless closed
collection beside an isolated root. -/
def mediateFoundation : Profile Unit (Option Nat) where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding structure, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := fun _ a b => ∃ n, a = some (n+1) ∧ b = some n

/-- An abstract supplier: `none` is not concrete and grounds every `some n`;
`some (n+1)` grounds `some n`. -/
def abstractSupplier : Profile Unit (Option Nat) where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun x => x ≠ none
  grounds := fun _ a b => (a = none ∧ b ≠ none) ∨ ∃ n, a = some (n+1) ∧ b = some n

/-- With foundation through intermediaries only, the closed-collection condition
fails although an actual root exists. -/
def MediateFoundationControl : Prop :=
  ¬ ClosedGroundingCollectionsRooted mediateFoundation () ∧
  ActualRoot mediateFoundation () none

/-- With an abstract supplier, the borrowed-reality principle over all modelled
suppliers holds while the concrete-supplier bridge and the closed-collection
condition fail. -/
def AbstractSupplierControl : Prop :=
  NoWhollyBorrowedCollection abstractSupplier () ∧
  ¬ ActualSuppliersOfConcretaConcrete abstractSupplier () ∧
  ¬ ClosedGroundingCollectionsRooted abstractSupplier ()

/-- All controls of the batch. -/
def Controls : Prop :=
  LimitGrounderControl ∧ PureRegressControl ∧ RootedCycleControl ∧ AttenuationSatisfiable ∧
    MediateFoundationControl ∧ AbstractSupplierControl

end Control

end TruthCore.Causality.ClosedGroundingRoots
