module

public import TruthCore.Causality.LogicalNecessityContrast

/-! Explicit analyst profiles for the omitted logical branch of the necessary-root
fork. These are scoped siblings, not a completion of generic NECESSARY_5.
The formula language, Holds and candidate identity remain fixed throughout.
No syntactic completeness or real-world applicability is asserted. -/
@[expose] public section
namespace TruthCore.Causality.LogicalNecessityProfiles
open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Case.Catholicism (Signature)

/-- NECESSARY_13: all valuations and worlds of the supplied frame. -/
def SelectedFrameValidity {W A : Type} (F : Frame W) (φ : Formula A) : Prop := Valid F φ

/-- NECESSARY_14: all frames on every small world type, all valuations and worlds.
This is semantic K validity for Modal.Formula, not validity of every logic. -/
def AllFrameKValidity {A : Type} (φ : Formula A) : Prop :=
  ∀ (W : Type) (F : Frame W), Valid F φ

/-- A stated local theory: every selected formula holds at this world. -/
def TheoryAt {W A : Type} (F : Frame W) (V : Valuation W A) (w : W)
    (Γ : Formula A → Prop) : Prop := ∀ ψ, Γ ψ → Holds F V w ψ

/-- NECESSARY_15: local semantic consequence of the stated theory, over all
valuations/worlds of the same frame. An inconsistent theory trivializes it. -/
def TheoryRelativeEntailment {W A : Type} (F : Frame W) (Γ : Formula A → Prop)
    (φ : Formula A) : Prop := ∀ V w, TheoryAt F V w Γ → Holds F V w φ

/-- Explicit nonvacuity guard for this theory and frame; no truth claim. -/
def JointModel {W A : Type} (F : Frame W) (Γ : Formula A → Prop) : Prop :=
  ∃ V w, TheoryAt F V w Γ

/-- A jointly satisfiable theory cannot entail falsum. -/
def NoFalsumConsequence {W A : Type} (F : Frame W) (Γ : Formula A → Prop) : Prop :=
  ¬ TheoryRelativeEntailment F Γ .falsum

/-- The local theory holds both here and at every accessible world. These are
exactly the points consumed by the truth-and-box bridge; no reflexivity needed. -/
def TheoryOnCone {W A : Type} (F : Frame W) (V : Valuation W A) (w : W)
    (Γ : Formula A → Prop) : Prop :=
  TheoryAt F V w Γ ∧ ∀ v, F.access w v → TheoryAt F V v Γ

/-- OPEN dictionary for the same bearer n and same formula φ at every world.
Neither φ's name nor candidate-domain inhabitation supplies this equivalence. -/
def ExistenceDictionary {W A B : Type} (o : Ontic W B) (V : Valuation W A)
    (φ : Formula A) (n : B) : Prop :=
  ∀ v, Holds o.frame V v φ ↔ o.ExistsAt v n

/-- The three selected profiles. Coverage of intended logical necessity and
exclusive choice remain OPEN; their extensions need not be disjoint. -/
inductive LogicalProfile where
  | selectedFrame | allFrameK | statedTheory
  deriving DecidableEq

def NecessaryByProfile {W A : Type} (p : LogicalProfile) (F : Frame W)
    (Γ : Formula A → Prop) (φ : Formula A) : Prop :=
  match p with
  | .selectedFrame => SelectedFrameValidity F φ
  | .allFrameK => AllFrameKValidity φ
  | .statedTheory => TheoryRelativeEntailment F Γ φ

/-- Same-formula truth and box in the selected interpretation. -/
def TrueAndBox {W A : Type} (F : Frame W) (V : Valuation W A) (w : W)
    (φ : Formula A) : Prop := Holds F V w φ ∧ Holds F V w (.box φ)

/-- The root facts are independent of any formula's logical status. -/
def RootFactsForBearer {W : Type} (σ : Signature) (m : Profile W σ.Being)
    (w : W) (n : σ.Being) : Prop := RootFacts σ m w n

namespace Fixture
/-- Universal Unit frame, reused from the existing root fixture. -/
def F : Frame Unit := NecessarySenseFork.Control.unitProfile.ontic.frame
def p : Formula Unit := .atom ()
def identity : Formula Unit := .imp p p
def atomTheory : Formula Unit → Prop := (· = p)
def emptyTheory : Formula Unit → Prop := fun _ => False
def falseTheory : Formula Unit → Prop := (· = .falsum)
def trueV : Valuation Unit Unit := fun _ _ => True
def falseV : Valuation Unit Unit := fun _ _ => False
def dead : Frame Unit := ⟨fun _ _ => False⟩
def tFormula : Formula Unit := .imp (.box p) p
/-- Theory holds at false, fails at its successor true. -/
def coneV : Valuation Bool Unit := fun w _ => w = false

/-- Controls compare one formula each: strict K→frame, strict frame→theory,
true-and-box not giving validity/empty-theory entailment, inconsistent theory
triviality, and actual-only theory admission failing to give box truth.
The joint model uses an inhabited universal frame, satisfiable atom theory and
the route's exact existence valuation; it is a model, not a God inference. -/
def Controls : Prop :=
  (SelectedFrameValidity F tFormula ∧ ¬ AllFrameKValidity tFormula) ∧
  (TheoryRelativeEntailment F atomTheory p ∧ ¬ SelectedFrameValidity F p) ∧
  (TrueAndBox F trueV () p ∧ ¬ TheoryRelativeEntailment F emptyTheory p) ∧
  ((∀ φ, TheoryRelativeEntailment F falseTheory φ) ∧ ¬ JointModel F falseTheory) ∧
  (JointModel F atomTheory ∧ TheoryOnCone F trueV () atomTheory ∧
    ExistenceDictionary NecessarySenseFork.Control.unitProfile.ontic trueV p () ∧
    RootFactsForBearer NecessarySenseFork.Control.unitSignature
      NecessarySenseFork.Control.unitProfile () ()) ∧
  (TheoryRelativeEntailment NecessarySenseFork.Control.stepFrame atomTheory p ∧
    TheoryAt NecessarySenseFork.Control.stepFrame coneV false atomTheory ∧
    ¬ Holds NecessarySenseFork.Control.stepFrame coneV false (.box p)) ∧
  (TheoryRelativeEntailment F atomTheory p ∧ ¬ TrueAndBox F falseV () p)
/-- Actual root at false, absent at the accessible true world. -/
def mismatchProfile : Profile Bool NecessarySenseFork.Control.unitSignature.Being where
  ontic := {
    frame := NecessarySenseFork.Control.stepFrame
    ExistsAt := fun w _ => w = false
    Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

def boolTrueV : Valuation Bool Unit := fun _ _ => True

/-- Same actual ontology, but no candidate is God. -/
def noGodSignature : Signature :=
  { NecessarySenseFork.Control.unitSignature with IsGod := fun _ => False }

/-- Omitting the dictionary permits a valid identity formula over a root
whose bearer fails box-existence. Omitting independent RootFacts permits a
jointly satisfiable, admitted, dictionary-correct theory without any God.
All rival fixtures preserve the formula in each compared cell. -/
def OmissionControls : Prop :=
  (TheoryRelativeEntailment mismatchProfile.ontic.frame emptyTheory identity ∧
    TheoryOnCone mismatchProfile.ontic.frame boolTrueV false emptyTheory ∧
    RootFactsForBearer NecessarySenseFork.Control.unitSignature mismatchProfile false () ∧
    ¬ ExistenceDictionary mismatchProfile.ontic boolTrueV identity () ∧
    ¬ NecessaryRootBoxK NecessarySenseFork.Control.unitSignature mismatchProfile false
      (fun _ _ => False)) ∧
  (TheoryRelativeEntailment F atomTheory p ∧ TheoryOnCone F trueV () atomTheory ∧
    ExistenceDictionary NecessarySenseFork.Control.unitProfile.ontic trueV p () ∧
    ¬ NecessaryRootBoxK noGodSignature NecessarySenseFork.Control.unitProfile ()
      (fun _ _ => False))
end Fixture
end TruthCore.Causality.LogicalNecessityProfiles
