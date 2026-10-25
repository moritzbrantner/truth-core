import TruthCore.Modal.KResearch
import TruthCore.Modal.Cube

/-! Issue #267: stipulated S5 experiments, not historical attributions.
The shared domains and evaluator are reused. All conclusions retain their root,
component and proposition scope; no theological axiom is imported. -/
namespace TruthCore.Modal.S5Research
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Conception StrongBridge Contingent)

/-- Equivalence accessibility, using the existing modal cube's S5 basis. -/
def S5Frame {W : Type} (F : Frame W) : Prop := FrameSatisfies .S5 F

/-- One universal component: every supplied world is accessible from every other.
This is stronger than S5 alone, which permits disconnected components. -/
def Universal {W : Type} (F : Frame W) : Prop := ∀ w v, F.access w v

/-- Uniformity is agreement on D throughout the root's component, not identity. -/
def ComponentUniform {W : Type} (F : Frame W) (D : Domain W) (w : W) : Prop :=
  ∀ a b, F.access w a → F.access w b → Agree D a b

/-- The all-predicate route needs no extra world-extensionality axiom. -/
def Laws : Prop :=
  (∀ (W : Type) (F : Frame W) w, S5Frame F →
    (MC F allPredicates w ↔ Dia F (MC F allPredicates) w) ∧
    (MC F allPredicates w ↔ Box F (MC F allPredicates) w)) ∧
  (∀ (W : Type) (F : Frame W) w, S5Frame F →
    Dia F (MC F allPredicates) w → ComponentUniform F allPredicates w) ∧
  (∀ (W : Type) (F : Frame W) w, S5Frame F →
    Dia F (MC F allPredicates) w →
    (∀ P : MProp W, Dia F P w ↔ P w) ∧
    (∀ P : MProp W, P w ↔ Box F P w) ∧
    (∀ P : MProp W, ¬ Contingent F P w)) ∧
  (∀ (W : Type) (F : Frame W) w, S5Frame F → Universal F →
    Dia F (MC F allPredicates) w → ∀ v, v = w)

/-- The restricted route states classical negation closure and identity separately. -/
def LanguageLaws : Prop :=
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    S5Frame F → TruthCore.Logic.ExcludedMiddle →
    (∀ P, D P → D (fun v => ¬ P v)) → Dia F (MC F D) w →
    ComponentUniform F D w ∧ MC F D w ∧ Box F (MC F D) w ∧
    (∀ P, D P → (Dia F P w ↔ P w)) ∧
    (∀ P, D P → ¬ Contingent F P w)) ∧
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    S5Frame F → TruthCore.Logic.ExcludedMiddle →
    (∀ P, D P → D (fun v => ¬ P v)) → PropositionalExtensionality D →
    Dia F (MC F D) w → ∀ v, F.access w v → v = w) ∧
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    S5Frame F → Universal F → TruthCore.Logic.ExcludedMiddle →
    (∀ P, D P → D (fun v => ¬ P v)) → PropositionalExtensionality D →
    Dia F (MC F D) w → ∀ v, v = w)

inductive World where | root | left | right deriving DecidableEq, Repr

/-- A singleton root component and a separate two-world universal component. -/
def disconnected : Model World Unit where
  worlds := [.root, .left, .right]
  complete := by
    intro w
    cases w with
    | root => exact .head _
    | left => exact .tail _ (.head _)
    | right => exact .tail _ (.tail _ (.head _))
  edge := fun w => match w with
    | .root => fun v => match v with
      | .root => true | .left => false | .right => false
    | .left => fun v => match v with
      | .root => false | .left => true | .right => true
    | .right => fun v => match v with
      | .root => false | .left => true | .right => true
  atom := fun w _ => match w with
    | .root => true | .left => true | .right => false

/-- Universal two-world frame with a separating atom. -/
def pair : Model Bool Unit where
  worlds := [false, true]
  complete := by
    intro w
    cases w with
    | false => exact .head _
    | true => exact .tail _ (.head _)
  edge := fun _ _ => true
  atom := fun w _ => w

/-- A one-world model; possible collapse is coherent when contingency is absent. -/
def singleton : Model Unit Unit where
  worlds := [()]
  complete := by intro w; cases w; exact .head _
  edge := fun _ _ => true
  atom := fun _ _ => true

def pairP : MProp Bool := fun w => pair.atom w () = true

def emptyC : Conception Bool := fun _ _ => False

def indiscriminateC : Conception Bool := fun _ _ => True

def witnessedC : Conception Unit := fun P _ => P ()

/-- Finite assumption tests. Restricted-language collapse does not identify labels;
contingency outside that language cannot be substituted into its no-contingency law. -/
def Countermodels : Prop :=
  S5Frame disconnected.frame ∧
  MC disconnected.frame allPredicates .root ∧
  Dia disconnected.frame (MC disconnected.frame allPredicates) .root ∧
  Box disconnected.frame (MC disconnected.frame allPredicates) .root ∧
  (¬ MC disconnected.frame allPredicates .left) ∧
  (¬ Universal disconnected.frame) ∧
  World.left ≠ World.root ∧
  S5Frame duplicates.frame ∧ Universal duplicates.frame ∧
  MC duplicates.frame (expressible duplicates.frame duplicates.valuation) false ∧
  (¬ MC duplicates.frame allPredicates false) ∧
  (¬ PropositionalExtensionality (expressible duplicates.frame duplicates.valuation)) ∧
  Contingent duplicates.frame (fun w => w = true) false ∧
  (¬ expressible duplicates.frame duplicates.valuation (fun w => w = true)) ∧
  S5Frame pair.frame ∧ Universal pair.frame ∧ Contingent pair.frame pairP false ∧
  StrongBridge pair.frame emptyC false ∧
  (¬ emptyC (MC pair.frame allPredicates) false) ∧
  indiscriminateC (MC pair.frame allPredicates) false ∧
  (¬ StrongBridge pair.frame indiscriminateC false) ∧
  S5Frame singleton.frame ∧ Universal singleton.frame ∧
  StrongBridge singleton.frame witnessedC () ∧
  witnessedC (MC singleton.frame allPredicates) () ∧
  (∀ P : MProp Unit, ¬ Contingent singleton.frame P ()) ∧
  MC deadEnd.frame allPredicates () ∧
  Box deadEnd.frame (MC deadEnd.frame allPredicates) () ∧
  (¬ Dia deadEnd.frame (MC deadEnd.frame allPredicates) ()) ∧
  (¬ S5Frame deadEnd.frame) ∧
  eval pair false (.diamond (.atom ())) = true ∧
  eval pair false (.diamond (.neg (.atom ()))) = true ∧
  witnesses pair false (.atom ()) = [true] ∧
  witnesses pair false (.neg (.atom ())) = [false]

/-- Deliberately only one atom, not the full negation-closed formula language. -/
def atomOnly : Domain Bool := corpusDomain (fun _ : Unit => pairP)

/-- World extensionality alone does not replace negation closure. The atom-only
inventory separates the two labels but is not a full fixed modal language. -/
def DomainBoundary : Prop :=
  S5Frame pair.frame ∧ Universal pair.frame ∧ PropositionalExtensionality atomOnly ∧
  MC pair.frame atomOnly false ∧ Dia pair.frame (MC pair.frame atomOnly) true ∧
  (¬ MC pair.frame atomOnly true) ∧ Contingent pair.frame pairP true ∧
  atomOnly pairP ∧ (¬ atomOnly (fun v => ¬ pairP v))

/-- Dropping symmetry while retaining reflexivity/transitivity permits possible
full collapse and independently witnessed contingency at the same root. -/
def SymmetryBoundary : Prop :=
  let F := TruthCore.Modern.Hume.Conceivability.branching
  Reflexive F ∧ Transitive F ∧ (¬ Symmetric F) ∧
  Dia F (MC F allPredicates) false ∧
  (¬ MC F allPredicates false) ∧
  Contingent F (fun w => w = true) false

/-- Open applied premise: adopting S5 for this interpreted scenario. -/
def ScenarioFrame {W : Type} (F : Frame W) : Prop := S5Frame F
/-- Open applied premise, not attributed to Hume: all conceived predicates are possible. -/
def ScenarioBridge {W : Type} (F : Frame W) (C : Conception W) (w : W) : Prop :=
  StrongBridge F C w
/-- Independent open applied premise: both alternatives of P are accessible at w. -/
def ScenarioContingency {W : Type} (F : Frame W) (P : MProp W) (w : W) : Prop :=
  Contingent F P w
/-- Scoped reductio assumption in the projection, discharged rather than adopted. -/
def ConceivedCollapse {W : Type} (F : Frame W) (C : Conception W) (w : W) : Prop :=
  C (MC F allPredicates) w
/-- A conditional rejection of C(MC), not a claim that a source asserted it. -/
def CollapseConceptionExcluded {W : Type} (F : Frame W) (C : Conception W) (w : W) : Prop :=
  ¬ C (MC F allPredicates) w

/-- Deterministic report; exact witnesses and edges remain inspectable. -/
def report : String :=
  reprStr (disconnected.worlds.map (fun w =>
    (w, disconnected.worlds.map (fun v => (v, disconnected.edge w v)),
      eval disconnected w (.atom ()), eval disconnected w (.box (.atom ())),
      eval disconnected w (.diamond (.atom ())))),
    pair.worlds.map (fun w => (w, witnesses pair w (.atom ()),
      witnesses pair w (.neg (.atom ())))))
end TruthCore.Modal.S5Research
