module

public import TruthCore.Explanation.StoppingPoints
public import TruthCore.Explanation.ExplanatoryAdequacy
public import TruthCore.Explanation.CondensationSufficiency
public import TruthCore.Logic.ExcludedMiddle

/-! Analyst framework for #545 A–D. Modal truth, admitted complete-ground sets,
immediate membership dependencies and enabling rules are distinct parameters.
No source is credited with these policies. No relation is efficient causation by
its name; actuality and metaphysical applicability remain open. -/

@[expose] public section
namespace TruthCore.Explanation.GroundingBaseline
open TruthCore.Explanation.PSRStrength
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic.Regress
open TruthCore.Logic (ExcludedMiddle)

/-- Existence and rigid identity atoms reuse the existing modal language. -/
abbrev ModalAtom (B : Type) := Sum B (B × B)
def valuation (m : Ontic W B) : TruthCore.Modal.Valuation W (ModalAtom B)
  | w, .inl b => m.ExistsAt w b
  | _, .inr p => p.1 = p.2

/-- Independent candidate existential-ground relation, not `Ontic.Causes`. -/
structure Extension (W B : Type) where
  ontic : Ontic W B
  grounds : W → B → B → Prop

def SameModal (M N : Extension W B) : Prop :=
  (∀ w v, M.ontic.frame.access w v ↔ N.ontic.frame.access w v) ∧
  (∀ w b, M.ontic.ExistsAt w b ↔ N.ontic.ExistsAt w b)

def ModalTruth (M : Extension W B) (w : W) (p : TruthCore.Modal.Formula (ModalAtom B)) :=
  TruthCore.Modal.Holds M.ontic.frame (valuation M.ontic) w p

def EndpointSound (M : Extension W B) : Prop :=
  ∀ w r f, M.grounds w r f → M.ontic.ExistsAt w r ∧ M.ontic.ExistsAt w f ∧ r ≠ f

def LocalFounded (M : Extension W B) : Prop := ∀ w, WellFounded (M.grounds w)

def modalOntic : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w b => b = true ∨ w = false
  Causes := fun _ _ _ => False

def ungrounded : Extension Bool Bool := ⟨modalOntic, fun _ _ _ => False⟩
def grounded : Extension Bool Bool :=
  ⟨modalOntic, fun w r f => w = false ∧ r = true ∧ f = false⟩

def ModalIndependence : Prop :=
  (∀ (W B : Type) (M N : Extension W B), SameModal M N →
    ∀ w p, ModalTruth M w p ↔ ModalTruth N w p) ∧
  (SameModal ungrounded grounded ∧ EndpointSound ungrounded ∧ EndpointSound grounded ∧
    LocalFounded ungrounded ∧ LocalFounded grounded ∧
    (∀ w v, modalOntic.frame.access w v) ∧
    ContingentAt modalOntic false false ∧
    (¬ ∃ r, ungrounded.grounds false r false) ∧
    (∃ r, grounded.grounds false r false))

/- Export the existing boxed-fact notion; no second necessity semantics. -/
export TruthCore.Explanation.StoppingPoints (NecessaryFact)

def NecessaryImplication (A : Arena W B F) (a : W) (q p : F) : Prop :=
  ∀ v, Access A a v → A.holds v q → A.holds v p

def pairArena (p q : Bool → Prop) : Arena Bool Empty Bool :=
  basic everywhere (fun w f => if f then q w else p w)
    (fun _ _ _ => False) (fun f g => f = g)

def noC := pairArena (fun _ => True) (fun _ => True)
def noN := pairArena (fun w => w = false) (fun w => w = false)
def noS := pairArena (fun w => w = false) (fun _ => True)

def NecessitationCore : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (p q : F),
    Contingent A a p → NecessaryFact A a q → NecessaryImplication A a q p → False) ∧
  (¬ Contingent noC false false ∧ NecessaryFact noC false true ∧
    NecessaryImplication noC false true false) ∧
  (Contingent noN false false ∧ ¬ NecessaryFact noN false true ∧
    NecessaryImplication noN false true false) ∧
  (Contingent noS false false ∧ NecessaryFact noS false true ∧
    ¬ NecessaryImplication noS false true false)

/-- Actual candidates are arbitrary predicate-valued sets, not one chosen
explanans. Admission alone entails none of the policies below. -/
abbrev FullGround (F : Type) := (F → Prop) → F → Prop

def ActualMembers (A : Arena W B F) (a : W) (G : FullGround F) : Prop :=
  ∀ S f, G S f → ∀ r, S r → A.holds a r

def LinkedMembers (R : F → F → Prop) (G : FullGround F) : Prop :=
  ∀ S f, G S f → ∀ r, S r → R r f

/-- The entire set includes every relevant enabling condition. Sufficiency is
an explicit modal policy, not a definition of adequate explanation. -/
def JointNecessitation (A : Arena W B F) (a : W) (G : FullGround F) : Prop :=
  ∀ S f, G S f → ∀ v, Access A a v → (∀ r, S r → A.holds v r) → A.holds v f

def UngroundedContingent (A : Arena W B F) (a : W) (G : FullGround F) : Prop :=
  ∃ f, Contingent A a f ∧ ¬ ∃ S, G S f

def EveryContingentComplete (A : Arena W B F) (a : W) (G : FullGround F) : Prop :=
  ∀ f, Contingent A a f → ∃ S, G S f

/-- An explicit adapter for the already certified contingent-reason descent.
Only the ordering R is admitted as a reason at a; its philosophical meaning is
not identified with the original arena's explains relation. -/
def reasonView (A : Arena W B F) (a : W) (R : F → F → Prop) : Arena W B F :=
  { A with explains := fun w r f => w = a ∧ R r f }

def falseMember : Arena Bool Empty Bool :=
  pairArena (fun w => w = false) (fun _ => False)
def singletonFull (S : F → Prop) (f : F) : FullGround F :=
  fun T g => T = S ∧ g = f

def falseG : FullGround Bool := singletonFull (fun r => r = true) false
def falseR (r f : Bool) : Prop := r = true ∧ f = false

def bothCont : Arena Bool Empty Bool := pairArena (fun w => w = false) (fun w => w = false)
def selfG : FullGround Bool := fun S f => S = (fun r => r = f)
def emptyG : FullGround Bool := fun S _ => S = (fun _ => False)
def emptyR (_ _ : F) : Prop := False

def chainArena : Arena Bool Empty Nat :=
  basic everywhere (fun w _ => w = false) (fun _ _ _ => False) (fun f g => f = g)
def chainG : FullGround Nat := fun S f => S = (fun r => r = f + 1)
def chainR := TruthCore.Causality.SuccessorBorrowingLink

def bruteArena : Arena Bool Empty Unit :=
  basic everywhere (fun w _ => w = false) (fun _ _ _ => False) (fun f g => f = g)
def noG : FullGround F := fun _ _ => False

def ContingentTerminus : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (R : F → F → Prop)
      (G : FullGround F) (x : F),
    ExcludedMiddle → Contingent A a x → WellFounded R → ActualMembers A a G →
      LinkedMembers R G → JointNecessitation A a G → UngroundedContingent A a G) ∧
  (Contingent bruteArena false () ∧ WellFounded (emptyR : Unit → Unit → Prop) ∧
    ActualMembers bruteArena false noG ∧ LinkedMembers (emptyR : Unit → Unit → Prop) noG ∧
    JointNecessitation bruteArena false noG ∧ UngroundedContingent bruteArena false noG) ∧
  (Contingent falseMember false false ∧ WellFounded falseR ∧
    ¬ ActualMembers falseMember false falseG ∧ LinkedMembers falseR falseG ∧
    JointNecessitation falseMember false falseG ∧ EveryContingentComplete falseMember false falseG) ∧
  (Contingent bothCont false false ∧ WellFounded (emptyR : Bool → Bool → Prop) ∧
    ActualMembers bothCont false selfG ∧ ¬ LinkedMembers emptyR selfG ∧
    JointNecessitation bothCont false selfG ∧ EveryContingentComplete bothCont false selfG) ∧
  (Contingent bothCont false false ∧ WellFounded (emptyR : Bool → Bool → Prop) ∧
    ActualMembers bothCont false emptyG ∧ LinkedMembers emptyR emptyG ∧
    ¬ JointNecessitation bothCont false emptyG ∧ EveryContingentComplete bothCont false emptyG) ∧
  (Contingent chainArena false 0 ∧ ¬ WellFounded chainR ∧
    ActualMembers chainArena false chainG ∧ LinkedMembers chainR chainG ∧
    JointNecessitation chainArena false chainG ∧ EveryContingentComplete chainArena false chainG)

inductive Event | baseA | baseB | effectA | effectB deriving DecidableEq
open Event

def groundRule (r f : Event) : Prop :=
  (r = baseA ∧ f = effectA) ∨ (r = baseB ∧ f = effectB)
def enables (r f : Event) : Prop :=
  (r = effectB ∧ f = effectA) ∨ (r = effectA ∧ f = effectB)
def fullDependency (r f : Event) : Prop := groundRule r f ∨ enables r f

def active (on : Bool) : Event → Prop
  | baseA | baseB => True
  | effectA | effectB => on = true

/-- Candidate local rules, not asserted full explanations: one base and every
enabling condition must hold. Bases stay on in both fixed assignments. -/
def SatisfiesRules (on : Bool) : Prop :=
  ∀ f, f = effectA ∨ f = effectB →
    (active on f ↔ ∃ r, groundRule r f ∧ active on r ∧ ∀ e, enables e f → active on e)

def ruleArena : Arena Bool Empty Event :=
  basic everywhere (fun w => active (!w)) (fun _ _ _ => False) (fun f g => f = g)
def dependencyGraph : Graph Event := ⟨fullDependency⟩

def EnablingCycle : Prop :=
  WellFounded groundRule ∧ (Graph.mk groundRule).NoCycles ∧
  SatisfiesRules true ∧ SatisfiesRules false ∧
  (∀ w, ruleArena.holds w baseA ∧ ruleArena.holds w baseB) ∧
  Contingent ruleArena false effectA ∧ Contingent ruleArena false effectB ∧
  effectA ≠ effectB ∧
  TruthCore.Explanation.CondensationSufficiency.comp dependencyGraph effectA =
    TruthCore.Explanation.CondensationSufficiency.comp dependencyGraph effectB ∧
  Relation.TransGen fullDependency effectA effectA ∧ ¬ WellFounded fullDependency
/-- Exact raw-modal specialization for the existing finite configuration tool.
The arena is computed data; no proof or policy is hidden in a profile role. -/
def conditionArena (K : TruthCore.Modal.Frame W) (truth : W → F → Prop) : Arena W Empty F :=
  basic K.access truth (fun _ _ _ => False) (fun f g => f = g)
def ConditionContingent (K : TruthCore.Modal.Frame W) (truth : W → F → Prop) (a : W) (p : F) : Prop :=
  Contingent (conditionArena K truth) a p
def ConditionNecessary (K : TruthCore.Modal.Frame W) (truth : W → F → Prop) (a : W) (q : F) : Prop :=
  NecessaryFact (conditionArena K truth) a q
def ConditionImplication (K : TruthCore.Modal.Frame W) (truth : W → F → Prop) (a : W) (q p : F) : Prop :=
  NecessaryImplication (conditionArena K truth) a q p

end TruthCore.Explanation.GroundingBaseline
