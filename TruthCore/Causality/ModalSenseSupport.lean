module

public import TruthCore.Causality.NecessarySenseFork
public import TruthCore.Modal.StandardCorrespondenceCertificate
public import TruthCore.Modal.ConvergenceCertificate
public import TruthCore.Modal.NecessaryPotentialCausers
public import TruthCore.Modal.SimplicityCollapse

/-!
# Modal-logic support for the frame-class senses of "necessary"

Analyst formulation, attribution deferred (owner direction on the modal
library, 2026-11-07, issue #1233). The sense fork of the necessary-classical-God
route (`TruthCore.Causality.NecessarySenseFork`) reads "necessary being" as
box-existence of the root `n` in the route's Kripke frame `m.ontic.frame`
(NECESSARY_2, `NecessaryAt`, which is the Kripke box of `TruthCore.Modal.Kripke`
by `Iff.rfl`). Its T, S4, KTB and S5 branches need a frame condition on that
frame. The fork took the frame condition as an OPEN semantic premise.

This module states the frame conditions instead as modal PRINCIPLES about the
route's own necessity: the T, 4, B and 5 schemas are valid on the route's frame
(true at every world under every valuation of one sentence letter). The
correspondence theorems of the modal library turn each schema into its frame
condition:

* `StandardCorrespondenceCertificate`: the T schema `□p → p` is valid on a
  frame iff the frame is reflexive;
* `ConvergenceCertificate`: the 4 schema `□p → □□p` (Lemmon-Scott
  `convergenceFormula 0 1 2 0`) is valid iff the frame is transitive, the B
  schema `p → □◇p` (`0 0 1 1`) iff symmetric, the 5 schema `◇p → □◇p`
  (`1 0 1 1`) iff Euclidean.

The necessity in the schemas is the frame's box over the route's worlds
(complete possible histories), the same box as NECESSARY_2; the sentence letter
ranges over all valuations, so validity is a principle about every proposition
of the frame, not only about existence. No logical necessity, essence-based
necessary existence or tertia via "cannot not-be" is involved.

`IntendedIsBoxT` etc. fix the reading of "necessary" to one frame-class sense
(coverage and exclusivity of the fork in one premise, for one constructor).

`DistinctNecessaryPotentialCausers` is a recorded rival (ditheism in modal
form): two distinct beings, each necessary at `w` and each a possible cause of
every other being existing at any accessible world.

`NecessaryActStrictlyYieldsContingent` records the combination that the
modal-collapse objection to a simple necessary root (#462, #555) turns on: an
act token performed at every world accessible from `w`, strictly efficacious
for an effect (the effect exists wherever the token is performed) that is
nevertheless contingent at `w`.
-/

@[expose] public section

namespace TruthCore.Causality.ModalSenseSupport

open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt)
open TruthCore.Modal.ExistenceDegrees (OtherDirectedPotentialCause)

variable {W B : Type}

/-! ## Modal principles about the route's necessity (OPEN premises) -/

/-- OPEN premise (NECESSARY_2 in KT): the T schema `□p → p` is valid on the
route's frame: whatever is necessary at a world is true there, for every
proposition (every valuation of the sentence letter) and every world. -/
def OnticTSchemaValid (o : Ontic W B) : Prop :=
  Valid o.frame (.imp (.box (.atom ())) (.atom ()) : Formula Unit)

/-- OPEN premise (NECESSARY_2 in S4): the 4 schema `□p → □□p` is valid on the
route's frame: whatever is necessary is necessarily necessary. -/
def Ontic4SchemaValid (o : Ontic W B) : Prop :=
  Valid o.frame (convergenceFormula 0 1 2 0)

/-- OPEN premise (NECESSARY_2 in KTB): the B schema `p → □◇p` is valid on the
route's frame: whatever is true is necessarily possible. -/
def OnticBSchemaValid (o : Ontic W B) : Prop :=
  Valid o.frame (convergenceFormula 0 0 1 1)

/-- OPEN premise (NECESSARY_2 in S5): the 5 schema `◇p → □◇p` is valid on the
route's frame: whatever is possible is necessarily possible. -/
def Ontic5SchemaValid (o : Ontic W B) : Prop :=
  Valid o.frame (convergenceFormula 1 0 1 1)

/-! ## Reading choices (OPEN premises, one per frame-class sense) -/

/-- OPEN reading premise: the route's intended reading of "necessary" is
exactly box-existence in frame class KT (`Sense.boxT`). -/
def IntendedIsBoxT (Intended : Sense → Prop) : Prop := ∀ s, Intended s ↔ s = .boxT

/-- OPEN reading premise: the intended reading is exactly box-existence in S4. -/
def IntendedIsBoxS4 (Intended : Sense → Prop) : Prop := ∀ s, Intended s ↔ s = .boxS4

/-- OPEN reading premise: the intended reading is exactly box-existence in KTB. -/
def IntendedIsBoxB (Intended : Sense → Prop) : Prop := ∀ s, Intended s ↔ s = .boxB

/-- OPEN reading premise: the intended reading is exactly box-existence in S5. -/
def IntendedIsBoxS5 (Intended : Sense → Prop) : Prop := ∀ s, Intended s ↔ s = .boxS5

/-! ## A recorded rival -/

/-- Rival (modal ditheism): two distinct beings are each necessary at `w`
(NECESSARY_2) and each a possible cause of every other being that exists at any
world accessible from `w`. -/
def DistinctNecessaryPotentialCausers (o : Ontic W B) (w : W) : Prop :=
  ∃ a b, a ≠ b ∧ NecessaryAt o w a ∧ OtherDirectedPotentialCause o w a ∧
    NecessaryAt o w b ∧ OtherDirectedPotentialCause o w b

/-- Constraint candidate (#462, #555): some frame, act token and effect have the
token performed at every accessible world, strict efficacy of the token for the
effect, and a contingent effect. -/
def NecessaryActStrictlyYieldsContingent : Prop :=
  ∃ (W B A : Type) (p : TruthCore.Modal.SelectedEffectBridge.OutputProfile W B A) (w : W) (a : A)
    (x : B), TruthCore.Modal.SelectedEffectBridge.SameActEverywhere p w a ∧
      TruthCore.Modal.SimplicityCollapse.StrictEfficacy p w a x ∧
      TruthCore.German.Kant.CosmologicalInference.ContingentAt p.ontic w x

end TruthCore.Causality.ModalSenseSupport

/-! ## Controls (formal, finite) -/

namespace TruthCore.Causality.ModalSenseSupport.Control

open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.ModalSenseSupport
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessarySenseFork.Control (unitSignature unitProfile)

/-- The single being of `unitSignature` exists at every world of the frame `F`,
is concrete and has no ground: the K node holds at every world of every frame. -/
def everywhere {W : Type} (F : Frame W) : Profile W unitSignature.Being where
  ontic := { frame := F, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- One-point universal frame on which the single being exists nowhere. -/
def nowhere : Profile Unit unitSignature.Being where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => False, Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Two worlds; every world accesses only `true`: `false` does not access itself. -/
def stepFrame : Frame Bool := ⟨fun _ b => b = true⟩

/-- Two worlds ordered `false ≤ true`: reflexive and transitive, neither
symmetric nor Euclidean. Hand-written, no Mathlib order instance. -/
def leFrame : Frame Bool := ⟨fun a b => a = false ∨ b = true⟩

/-- No causes of necessity (the per se relation is unused by the frame senses). -/
def noCN : unitSignature.Being → unitSignature.Being → Prop := fun _ _ => False

/-- Nonvacuity: on the one-point universal frame the four schemas are valid,
the K node holds, and each frame-class fork node holds on its selected reading. -/
def Nonvacuity : Prop :=
  OnticTSchemaValid unitProfile.ontic ∧ Ontic4SchemaValid unitProfile.ontic ∧
  OnticBSchemaValid unitProfile.ontic ∧ Ontic5SchemaValid unitProfile.ontic ∧
  NecessaryRootBoxK unitSignature unitProfile () noCN ∧
  NecessaryRootOnIntendedReading (· = Sense.boxT) unitSignature unitProfile () noCN ∧
  NecessaryRootOnIntendedReading (· = Sense.boxS4) unitSignature unitProfile () noCN ∧
  NecessaryRootOnIntendedReading (· = Sense.boxB) unitSignature unitProfile () noCN ∧
  NecessaryRootOnIntendedReading (· = Sense.boxS5) unitSignature unitProfile () noCN

/-- Omission models, one per load-bearing premise of the four branches:
1. T schema omitted (non-reflexive step frame): K node and T reading hold, the T
   fork fails;
2. 4 schema omitted (reflexive non-transitive chain): T schema valid, the S4 fork fails;
3. B schema omitted (`false ≤ true`): T schema valid, the KTB fork fails;
4. 5 schema omitted (`false ≤ true`): T schema valid, the S5 fork fails;
5. reading choice omitted (every sense intended): all schemas valid, the K node
   holds, no fork node holds;
6. K node omitted (the being exists nowhere): all schemas valid, the T reading
   holds, the T fork fails. -/
def Omissions : Prop :=
  (NecessaryRootBoxK unitSignature (everywhere stepFrame) false noCN ∧
    ¬ OnticTSchemaValid (everywhere stepFrame).ontic ∧ IntendedIsBoxT (· = Sense.boxT) ∧
    ¬ NecessaryRootOnIntendedReading (· = Sense.boxT) unitSignature (everywhere stepFrame) false noCN) ∧
  (NecessaryRootBoxK unitSignature (everywhere NecessarySenseFork.Control.chainFrame) 0 noCN ∧
    OnticTSchemaValid (everywhere NecessarySenseFork.Control.chainFrame).ontic ∧
    ¬ Ontic4SchemaValid (everywhere NecessarySenseFork.Control.chainFrame).ontic ∧
    IntendedIsBoxS4 (· = Sense.boxS4) ∧
    ¬ NecessaryRootOnIntendedReading (· = Sense.boxS4) unitSignature
      (everywhere NecessarySenseFork.Control.chainFrame) 0 noCN) ∧
  (NecessaryRootBoxK unitSignature (everywhere leFrame) false noCN ∧
    OnticTSchemaValid (everywhere leFrame).ontic ∧ ¬ OnticBSchemaValid (everywhere leFrame).ontic ∧
    IntendedIsBoxB (· = Sense.boxB) ∧
    ¬ NecessaryRootOnIntendedReading (· = Sense.boxB) unitSignature (everywhere leFrame) false noCN) ∧
  (NecessaryRootBoxK unitSignature (everywhere leFrame) false noCN ∧
    OnticTSchemaValid (everywhere leFrame).ontic ∧ ¬ Ontic5SchemaValid (everywhere leFrame).ontic ∧
    IntendedIsBoxS5 (· = Sense.boxS5) ∧
    ¬ NecessaryRootOnIntendedReading (· = Sense.boxS5) unitSignature (everywhere leFrame) false noCN) ∧
  (NecessaryRootBoxK unitSignature unitProfile () noCN ∧
    OnticTSchemaValid unitProfile.ontic ∧ Ontic4SchemaValid unitProfile.ontic ∧
    OnticBSchemaValid unitProfile.ontic ∧ Ontic5SchemaValid unitProfile.ontic ∧
    ¬ NecessaryRootOnIntendedReading (fun _ => True) unitSignature unitProfile () noCN) ∧
  (OnticTSchemaValid nowhere.ontic ∧ Ontic4SchemaValid nowhere.ontic ∧
    OnticBSchemaValid nowhere.ontic ∧ Ontic5SchemaValid nowhere.ontic ∧
    IntendedIsBoxT (· = Sense.boxT) ∧
    ¬ NecessaryRootOnIntendedReading (· = Sense.boxT) unitSignature nowhere () noCN)

/-- The two recorded rivals are exactly negated by existing modal-library
conclusions: `NoDistinctNecessaryPotentialCausers` is equivalent to the negation
of modal ditheism, and the first clause of `SimplicityCollapse.Core` excludes
`NecessaryActStrictlyYieldsContingent`. -/
def RivalNegations : Prop :=
  (∀ (W B : Type) (o : TruthCore.German.Kant.CosmologicalInference.Ontic W B) (w : W),
    TruthCore.Modal.NecessaryPotentialCausers.NoDistinctNecessaryPotentialCausers o w ↔
      ¬ DistinctNecessaryPotentialCausers o w) ∧
  (TruthCore.Modal.SimplicityCollapse.Core → ¬ NecessaryActStrictlyYieldsContingent)

/-- The batch controls. -/
def Controls : Prop := Nonvacuity ∧ Omissions ∧ RivalNegations

end TruthCore.Causality.ModalSenseSupport.Control
