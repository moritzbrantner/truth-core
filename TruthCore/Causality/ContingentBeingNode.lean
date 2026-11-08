module

public import TruthCore.Causality.ModalSenseSupport
public import TruthCore.Logic.CogitoConcrete
public import TruthCore.Modal.TResearch
public import TruthCore.Modal.BResearch
public import TruthCore.Modal.S5Research

/-!
# Some actual concrete being is contingent: the route's contingency node

Analyst formulation, attribution deferred (#1233). The necessary-classical-God
route never asserted that an actual concrete being is contingent, so the modal
library's collapse laws (#462, #555) contradicted nothing on it (triage:
`docs/notes/modal-results-triage.md`). This module adds that node,
`SomeActualContingentAt`, on the route's own `Profile`: some concrete
individual exists at `w` and is absent at some world accessible from `w`
(CONTINGENT_1, `ContingentAt`, DEF-KANT-MODAL-CONTINGENCY; not empirical
change, CONTINGENT_2 of DISAMB-KANT-CONTINGENCY). It is stronger than the
Cogito population node `InhabitedConcreteAt` and says nothing about which
being is contingent, why, or whether it is caused.

The rivals are modal-collapse readings, each stated on the route's frame
`m.ontic.frame` (the box is the frame's Kripke box, the same box as the route's
NECESSARY_2 box-existence):

* `EveryActualConcreteNecessaryAt`: every actual concrete being is NECESSARY_2
  (concrete necessitarianism; the contradictory of the node);
* `RouteCollapsedAt`: every truth at `w` is necessary at `w` (full modal collapse,
  the modal library's `MC _ allPredicates`; Spinoza/Hume necessitarianism);
* `RouteNecessarilyCollapsedAt`: collapse holds at every accessible world;
* `RoutePossiblyCollapsedAt`: collapse holds at some accessible world;
* `NecessaryActStrictlyYieldsAllAt`: some act token is performed at every
  accessible world and strictly yields every actual concrete being (a necessary
  sufficient cause of all, the collapse objection to a simple necessary creator).

Each `Not…`/`No…` declaration is the negation of one rival, named so that a
refutation's conclusion binds to its own statement.
-/

@[expose] public section

namespace TruthCore.Causality.ContingentBeingNode

open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Modal.SelectedEffectBridge (OutputProfile SameActEverywhere)
open TruthCore.Modal.SimplicityCollapse (StrictEfficacy)

variable {W B : Type}

/-! ## The node (OPEN premise) -/

/-- OPEN premise (CONTINGENT_1): some concrete individual exists at `w` and is
absent at some world accessible from `w`. -/
def SomeActualContingentAt (m : Profile W B) (w : W) : Prop :=
  ∃ x, m.concrete x ∧ ContingentAt m.ontic w x

/-! ## Rivals (modal collapse) -/

/-- Rival: every concrete individual existing at `w` is NECESSARY_2 at `w`
(exists at every accessible world). -/
def EveryActualConcreteNecessaryAt (m : Profile W B) (w : W) : Prop :=
  ∀ x, m.concrete x → m.ontic.ExistsAt w x → NecessaryAt m.ontic w x

/-- Rival: full modal collapse at `w` on the route's frame: every proposition
true at `w` is true at every accessible world. -/
def RouteCollapsedAt (o : Ontic W B) (w : W) : Prop :=
  MC o.frame allPredicates w

/-- Rival: full collapse holds at every world accessible from `w`. -/
def RouteNecessarilyCollapsedAt (o : Ontic W B) (w : W) : Prop :=
  Box o.frame (MC o.frame allPredicates) w

/-- Rival: full collapse holds at some world accessible from `w`. -/
def RoutePossiblyCollapsedAt (o : Ontic W B) (w : W) : Prop :=
  Dia o.frame (MC o.frame allPredicates) w

/-- Rival (necessary sufficient cause of all): some act token of some output
profile on the route's own `Ontic` is performed at every world accessible from
`w` and is strictly efficacious for every concrete individual existing at `w`
(each exists wherever the token is performed at an accessible world). -/
def NecessaryActStrictlyYieldsAllAt (m : Profile W B) (w : W) : Prop :=
  ∃ (A : Type) (p : OutputProfile W B A) (a : A), p.ontic = m.ontic ∧
    SameActEverywhere p w a ∧
    ∀ x, m.concrete x → m.ontic.ExistsAt w x → StrictEfficacy p w a x

/-! ## Negations (refutation conclusions) -/

/-- Not every actual concrete being is NECESSARY_2 at `w`. -/
def NotEveryActualConcreteNecessaryAt (m : Profile W B) (w : W) : Prop :=
  ¬ EveryActualConcreteNecessaryAt m w

/-- The route's world is not fully collapsed. -/
def RouteNotCollapsedAt (o : Ontic W B) (w : W) : Prop := ¬ RouteCollapsedAt o w

/-- Full collapse does not hold at every accessible world. -/
def RouteNotNecessarilyCollapsedAt (o : Ontic W B) (w : W) : Prop :=
  ¬ RouteNecessarilyCollapsedAt o w

/-- Full collapse holds at no accessible world. -/
def RouteNotPossiblyCollapsedAt (o : Ontic W B) (w : W) : Prop :=
  ¬ RoutePossiblyCollapsedAt o w

/-- No act token performed at every accessible world strictly yields every
actual concrete being. -/
def NoNecessaryActStrictlyYieldsAllAt (m : Profile W B) (w : W) : Prop :=
  ¬ NecessaryActStrictlyYieldsAllAt m w

end TruthCore.Causality.ContingentBeingNode

/-! ## Controls (formal, finite, hand-written carriers) -/

namespace TruthCore.Causality.ContingentBeingNode.Control

open TruthCore.Modal
open TruthCore.Causality.ContingentBeingNode
open TruthCore.Causality.ModalSenseSupport
open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Two worlds, both accessing each other and themselves (universal frame).
Being `true` exists at both worlds, being `false` only at world `false`. -/
def twoWorlds : Profile Bool Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w x => x = true ∨ w = false,
             Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ y => y = false

/-- One world, accessing itself; its one being exists there. -/
def oneWorld : Profile Unit Unit where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True,
             Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Non-reflexive, non-symmetric step frame: every world accesses only `true`.
Being `false` exists only at world `false`. -/
def step : Profile Bool Bool where
  ontic := { frame := ⟨fun _ b => b = true⟩, ExistsAt := fun w x => x = true ∨ w = false,
             Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Reflexive, transitive two-world frame `false ≤ true` (neither symmetric nor
Euclidean), with being `false` only at world `false`. -/
def le : Profile Bool Bool where
  ontic := { frame := ModalSenseSupport.Control.leFrame,
             ExistsAt := fun w x => x = true ∨ w = false, Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Nonvacuity: on `twoWorlds` at world `false` the node holds, the T, B and 5
schemas are valid, the Cogito node and the grounding premise hold, and every
rival fails. -/
def Nonvacuity : Prop :=
  SomeActualContingentAt twoWorlds false ∧
  OnticTSchemaValid twoWorlds.ontic ∧ OnticBSchemaValid twoWorlds.ontic ∧
  Ontic5SchemaValid twoWorlds.ontic ∧
  InhabitedConcreteAt twoWorlds.ontic twoWorlds.concrete false ∧
  EveryContingentGroundedAt twoWorlds false ∧
  NotEveryActualConcreteNecessaryAt twoWorlds false ∧
  RouteNotCollapsedAt twoWorlds.ontic false ∧
  RouteNotNecessarilyCollapsedAt twoWorlds.ontic false ∧
  RouteNotPossiblyCollapsedAt twoWorlds.ontic false ∧
  NoNecessaryActStrictlyYieldsAllAt twoWorlds false

/-- Omission models.
1. Node omitted (`oneWorld`): the T, B and 5 schemas are valid and every rival
   holds, so each refutation needs the node.
2. T schema omitted (`step`, world `false`): the node holds and full collapse
   holds at every accessible world, so the KT-sense refutation needs the T schema.
3. B schema omitted (`step`, world `false`): the node holds and full collapse
   holds at some accessible world, so the KTB-sense refutation needs the B schema.
4. 5 schema omitted (`le`, world `false`): the T schema is valid, the B and 5
   schemas are not, the node holds and full collapse holds at the accessible
   world `true`, so the S5-sense refutation needs the 5 schema (and neither
   possible-collapse refutation follows from the T schema alone). -/
def Omissions : Prop :=
  (OnticTSchemaValid oneWorld.ontic ∧ OnticBSchemaValid oneWorld.ontic ∧
    Ontic5SchemaValid oneWorld.ontic ∧ ¬ SomeActualContingentAt oneWorld () ∧
    EveryActualConcreteNecessaryAt oneWorld () ∧ RouteCollapsedAt oneWorld.ontic () ∧
    RouteNecessarilyCollapsedAt oneWorld.ontic () ∧ RoutePossiblyCollapsedAt oneWorld.ontic () ∧
    NecessaryActStrictlyYieldsAllAt oneWorld ()) ∧
  (SomeActualContingentAt step false ∧ ¬ OnticTSchemaValid step.ontic ∧
    RouteNecessarilyCollapsedAt step.ontic false) ∧
  (SomeActualContingentAt step false ∧ ¬ OnticBSchemaValid step.ontic ∧
    RoutePossiblyCollapsedAt step.ontic false) ∧
  (SomeActualContingentAt le false ∧ OnticTSchemaValid le.ontic ∧
    ¬ OnticBSchemaValid le.ontic ∧ ¬ Ontic5SchemaValid le.ontic ∧
    RoutePossiblyCollapsedAt le.ontic false)

/-- Scope: concrete necessitarianism makes the route premise
`EveryContingentGroundedAt` true vacuously, at every profile and world. So the
collapse rivals are rivals of the node, not of that grounding premise; and the
node is what makes the grounding premise apply to some actual being. -/
def Scope : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W),
    EveryActualConcreteNecessaryAt m w → EveryContingentGroundedAt m w

/-- The batch controls. -/
def Controls : Prop := Nonvacuity ∧ Omissions ∧ Scope

end TruthCore.Causality.ContingentBeingNode.Control
