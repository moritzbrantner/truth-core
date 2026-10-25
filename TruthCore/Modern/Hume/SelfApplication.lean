import TruthCore.Results.Modern.Hume.Conceivability.Solution

/-! Issue #268 extends, rather than repeats, #248. The modal laws below are
stipulated comparisons. No unrestricted or necessary bridge, higher-order
conception, or modal frame is attributed to Treatise I.3.3 §§1–7.
The source reading itself reuses STMT-HUME-NARROW-IDEAS-WITHHOLDING. -/
namespace TruthCore.Modern.Hume.SelfApplication
open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability

universe u

/-- Necessary denial and denial of the necessary bridge have different scopes. -/
def NecessaryDenial {W : Type u} (F : Frame W) (C : Conception W) : MProp W :=
  Box F (fun v => ¬ StrongBridge F C v)

/-- Conditional mathematical laws. The first two are composed from #248. -/
def HigherOrderLaws : Prop :=
  SelfApplicationLaw ∧ NecessaryConflictLaw ∧
  (∀ (W : Type) (F : Frame W) (C : Conception W) w,
    StrongBridge F C w → C (NecessaryDenial F C) w →
    Dia F (NecessaryDenial F C) w) ∧
  (∀ (W : Type) (F : Frame W) (C : Conception W) w,
    Reflexive F → StrongBridge F C w → Box F (StrongBridge F C) w →
    ¬ C (NecessaryDenial F C) w) ∧
  (∀ (W : Type) (F : Frame W) (C : Conception W) w,
    Transitive F → (∀ v, F.access w v → ∃ z, F.access v z) →
    StrongBridge F C w → Box F (StrongBridge F C) w →
    ¬ C (NecessaryDenial F C) w)

/-- Root false sees only a dead end true. No reflexivity or seriality is hidden. -/
def oneStep : Frame Bool := ⟨fun w v => w = false ∧ v = true⟩

/-- At false, exactly the propositions true at its successor are conceived;
at the dead end, nothing is conceived. -/
def oneStepConception : Conception Bool := fun P w => w = false ∧ P true

/-- The old selfC model and the new dead-end model separate the two conceptions.
The first also witnesses why possible failure of H is not actual failure. -/
def ScopeCountermodels : Prop :=
  (StrongBridge universal selfC false ∧
    selfC (fun v => ¬ StrongBridge universal selfC v) false ∧
    Dia universal (fun v => ¬ StrongBridge universal selfC v) false ∧
    ¬ selfC (NecessaryDenial universal selfC) false) ∧
  (StrongBridge oneStep oneStepConception false ∧
    Box oneStep (StrongBridge oneStep oneStepConception) false ∧
    oneStepConception (NecessaryDenial oneStep oneStepConception) false ∧
    ¬ oneStepConception (fun v => ¬ StrongBridge oneStep oneStepConception v) false ∧
    ¬ Reflexive oneStep ∧
    ¬ (∀ v, oneStep.access false v → ∃ z, oneStep.access v z))

/-- A tiny description language: being a grammatical description supplies no
consistency or imaginative-adequacy judgment. `collapse` is only a label
whose stipulated denotation is full-predicate MC. -/
inductive Description where
  | atom
  | collapse
  | neg (d : Description)
  | both (left right : Description)

def Description.denote (F : Frame Bool) : Description → MProp Bool
  | .atom => fun w => w = true
  | .collapse => Collapse F
  | .neg d => fun w => ¬ d.denote F w
  | .both a b => fun w => a.denote F w ∧ b.denote F w

/-- Pointwise denotation avoids treating predicate equality as an axiom. -/
def Verbal (F : Frame Bool) : Conception Bool :=
  fun P _ => ∃ d : Description, ∀ v, d.denote F v ↔ P v

/-- Model satisfiability somewhere is weaker than possibility from a given root. -/
def SatisfiableConception : Conception Bool := fun P _ => ∃ v, P v

/-- Defining conception as accessible possibility makes H true by definition;
it does not establish the adequacy of imagination or verbal description. -/
def ModalConception {W : Type u} (F : Frame W) : Conception W :=
  fun P w => Dia F P w

def identityFrame : Frame Bool := ⟨fun w v => w = v⟩

/-- Explicit alternatives, not competing historical readings silently identified. -/
def ConceptionModeChecks : Prop :=
  (∀ (W : Type) (F : Frame W) w, StrongBridge F (ModalConception F) w) ∧
  (¬ StrongBridge identityFrame SatisfiableConception false) ∧
  (Verbal universal (fun _ => False) false ∧ ¬ StrongBridge universal (Verbal universal) false) ∧
  (Verbal universal (Collapse universal) false ∧
    ¬ (fun _ _ => False : Conception Bool) (Collapse universal) false) ∧
  (NarrowWithholding (fun _ : Unit => False) () ∧
    StrongBridge universal (fun _ _ => False) false ∧
    ¬ StrongBridge universal indiscriminate false)
/-- Reflexivity at every world makes the separate actual-H hypothesis redundant.
This is a new, separately frozen strengthening, not an edit of HigherOrderLaws. -/
def ReflexiveConflictLaws : Prop :=
  ∀ (W : Type) (F : Frame W) (C : Conception W) w,
    Reflexive F → Box F (StrongBridge F C) w →
    (¬ C (fun v => ¬ StrongBridge F C v) w ∧
      ¬ C (NecessaryDenial F C) w)

inductive ChainWorld where
  | root
  | middle
  | last

def chain : Frame ChainWorld := ⟨fun w v =>
  match w with
  | .root => match v with
    | .root => False
    | .middle => True
    | .last => False
  | .middle => match v with
    | .root => False
    | .middle => False
    | .last => True
  | .last => match v with
    | .root => False
    | .middle => False
    | .last => True⟩

/-- The root trusts its middle successor, which conceives nothing. The last
world conceives everything and fails H. No epistemic warrant is asserted. -/
def chainConception : Conception ChainWorld := fun P w =>
  match w with
  | .root => P .middle
  | .middle => False
  | .last => True

/-- Like chainConception except for an indiscriminate unsound root. -/
def unsoundRoot : Conception ChainWorld := fun _ w =>
  match w with
  | .root => True
  | .middle => False
  | .last => True

/-- Seriality cannot replace transitivity for necessary-denial conflict. A
separate unsound-root witness shows that C(¬H) needs an actual bridge. -/
def DroppedPremiseModels : Prop :=
  ((∀ w, ∃ v, chain.access w v) ∧ ¬ Transitive chain ∧
    StrongBridge chain chainConception .root ∧
    Box chain (StrongBridge chain chainConception) .root ∧
    chainConception (NecessaryDenial chain chainConception) .root) ∧
  (unsoundRoot (fun v => ¬ StrongBridge chain unsoundRoot v) .root ∧
    ¬ Dia chain (fun v => ¬ StrongBridge chain unsoundRoot v) .root ∧
    ¬ StrongBridge chain unsoundRoot .root)
end TruthCore.Modern.Hume.SelfApplication
