module
public import TruthCore.Causality.JointGroups
@[expose] public section
namespace TruthCore.Causality.InterventionTransitivity

/-- Variables denote Boolean magnitudes, never concrete bearers. -/
inductive Variable where | x | y | z deriving DecidableEq

/-- Fixed background, recursive equations Y=f(X), Z=g(X,Y). -/
structure Model where
  actualX : Bool
  f : Bool → Bool
  g : Bool → Bool → Bool

def Model.actual (m : Model) : Variable → Bool
  | .x => m.actualX
  | .y => m.f m.actualX
  | .z => m.g m.actualX (m.f m.actualX)

/-- Replace exactly one equation by a constant; recompute descendants. -/
def Model.intervene (m : Model) (v : Variable) (b : Bool) : Variable → Bool :=
  let x := if v = .x then b else m.actualX
  let y := if v = .y then b else m.f x
  let z := if v = .z then b else m.g x y
  fun w => match w with | .x => x | .y => y | .z => z

/-- Typed actual-state dependence; diagonal comparisons excluded. -/
structure ButFor (m : Model) (a b : Variable) : Prop where
  distinct : a ≠ b
  changed : m.intervene a (!(m.actual a)) b ≠ m.actual b

/-- Declared input graph; an input slot may be functionally idle. -/
def inputGraph : TruthCore.Logic.Regress.Graph Variable :=
  ⟨fun a b => (a = .x ∧ b = .y) ∨ (a = .x ∧ b = .z) ∨ (a = .y ∧ b = .z)⟩

def cancellation : Model := ⟨true, id, fun x y => x == y⟩
def chain : Model := ⟨true, id, fun _ y => y⟩

def Witness : Prop :=
  cancellation.actual .x = true ∧ cancellation.actual .y = true ∧
  cancellation.actual .z = true ∧
  cancellation.intervene .x false .y = false ∧
  cancellation.intervene .x false .z = true ∧
  cancellation.intervene .y false .z = false ∧
  ButFor cancellation .x .y ∧ ButFor cancellation .y .z ∧
  ¬ ButFor cancellation .x .z

def ChainSchema : Prop := ∀ (x : Bool) (f g : Bool → Bool),
  ButFor ⟨x, f, fun _ y => g y⟩ .x .y →
  ButFor ⟨x, f, fun _ y => g y⟩ .y .z →
  ButFor ⟨x, f, fun _ y => g y⟩ .x .z

/-- Controlled direct effect at the counterfactual mediator value. -/
def CompensationSchema : Prop := ∀ m : Model,
  ButFor m .x .y → ButFor m .y .z → ¬ ButFor m .x .z →
  m.g m.actualX (m.f (!m.actualX)) ≠ m.g (!m.actualX) (m.f (!m.actualX))

/-- No direct functional influence at the changed mediator blocks cancellation. -/
def LocalExclusionSchema : Prop := ∀ m : Model,
  ButFor m .x .y → ButFor m .y .z →
  m.g m.actualX (m.f (!m.actualX)) = m.g (!m.actualX) (m.f (!m.actualX)) →
  ButFor m .x .z

/-- Local dependencies are necessary for the chain inference, as separate omissions. -/
def Omissions : Prop :=
  (let m : Model := ⟨true, fun _ => true, fun _ y => y⟩;
    ButFor m .y .z ∧ ¬ ButFor m .x .z) ∧
  (let m : Model := ⟨true, id, fun _ _ => true⟩;
    ButFor m .x .y ∧ ¬ ButFor m .x .z)

def Certificate : Prop := Witness ∧ ChainSchema ∧ CompensationSchema ∧
  LocalExclusionSchema ∧ Omissions ∧
  (ButFor chain .x .y ∧ ButFor chain .y .z ∧ ButFor chain .x .z) ∧
  JointGroups.ancestry inputGraph .x .z ∧
  (∀ a b c, JointGroups.ancestry inputGraph a b →
    JointGroups.ancestry inputGraph b c → JointGroups.ancestry inputGraph a c)
end TruthCore.Causality.InterventionTransitivity
