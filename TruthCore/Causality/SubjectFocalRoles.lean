module
public import TruthCore.Models.Order
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder

/-! Analyst subject/accident candidate, attribution deferred. This is neither the
full BEING_4 interpretation nor a historical reconstruction of pros hen.
The primary account is Substance x; the secondary account explicitly mentions
an existing substance as subject. Distinct extensions do not encode all rationes.
Inheres is primitive subject dependence, not efficient production. -/
@[expose] public section
namespace TruthCore.Causality.SubjectFocalRoles
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Secondary predication: x exists in a substance as its subject. -/
def Secondary {B : Type} (Substance : B → Prop) (Inheres : B → B → Prop)
    (x : B) : Prop := ∃ s, Substance s ∧ Inheres x s

/-- Role accounts are formulas, not two opaque Focal flags. -/
inductive Role where | primary | secondary

def Account {B : Type} (Substance : B → Prop) (Inheres : B → B → Prop) :
    Role → B → Prop
  | .primary => Substance
  | .secondary => Secondary Substance Inheres

/-- One-world candidate. All substances exist; each inherence edge has an
existing nonsubstantial dependent and a distinct substantial subject. Both
accounts are populated. No transitivity, production, scale, God or unique
primary-instance condition is stipulated. -/
def SubjectFocalReading {B : Type} (Exists Substance : B → Prop)
    (Inheres : B → B → Prop) : Prop :=
  (∀ s, Substance s → Exists s) ∧
  (∀ x s, Inheres x s → Exists x ∧ Substance s ∧ ¬ Substance x ∧ x ≠ s) ∧
  (∃ s, Substance s) ∧ ∃ x, Secondary Substance Inheres x

/-- Possession in this candidate, retaining both distinct role accounts. -/
def HasBeing {B : Type} (S : B → Prop) (I : B → B → Prop) (x : B) (_ : Unit) : Prop :=
  S x ∨ Secondary S I x

/-- Open role applicability to the creature predicate of the root interface. -/
def CreatureSubjectBridge {B : Type} (S : B → Prop) (I : B → B → Prop)
    (Creature : B → Prop) : Prop := ∀ x, Creature x → Secondary S I x

/-- Open common-instance condition, stronger than shared reference to a type
of subject: every secondary is in this SAME p. Other substances may exist. -/
def CommonCenter {B : Type} (S : B → Prop) (I : B → B → Prop) (p : B) : Prop :=
  S p ∧ ∀ x, Secondary S I x → I x p

/-- Open translation from subject dependence to productive cause of being.
Not part of SubjectFocalReading and not secured by the word 'analogy'. -/
def SubjectCauseBridge {B : Type} (I : B → B → Prop)
    (CausesIn : B → B → Unit → Prop) : Prop := ∀ x s, I x s → CausesIn s x ()

/-- Scalar calibration is an independently supplied biconditional. -/
def Calibration {B D : Type} [Preorder D] (More : Unit → B → B → Prop)
    (near : B → D) : Prop := ∀ x y, More () x y ↔ near y < near x

def DegreeComparable {B D : Type} [Preorder D] (near : B → D) : Prop :=
  ∀ x y, near x ≤ near y ∨ near y ≤ near x

namespace Control
inductive B where | subject0 | subject1 | accident0 | accident1
  deriving DecidableEq
instance : OfNat B 0 := ⟨B.subject0⟩
instance : OfNat B 1 := ⟨B.subject1⟩
instance : OfNat B 2 := ⟨B.accident0⟩
instance : OfNat B 3 := ⟨B.accident1⟩

instance forallB {p : B → Prop} [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p 0 ∧ p 1 ∧ p 2 ∧ p 3)
    ⟨fun h x => by cases x; exact h.1; exact h.2.1; exact h.2.2.1; exact h.2.2.2,
     fun h => ⟨h 0, h 1, h 2, h 3⟩⟩
instance existsB {p : B → Prop} [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p 0 ∨ p 1 ∨ p 2 ∨ p 3)
    ⟨fun h => h.elim (fun h => ⟨0, h⟩) (fun h => h.elim (fun h => ⟨1, h⟩)
      (fun h => h.elim (fun h => ⟨2, h⟩) (fun h => ⟨3, h⟩))),
     fun ⟨x, h⟩ => by cases x; exact .inl h; exact .inr (.inl h);
                         exact .inr (.inr (.inl h)); exact .inr (.inr (.inr h))⟩
def existsAt : B → Prop := fun _ => True
def substance (x : B) : Prop := x = 0 ∨ x = 1
/-- Two accidents depend on the same subject 0; subject 1 also exists. -/
def common (x s : B) : Prop := (x = 2 ∨ x = 3) ∧ s = 0
/-- Same carrier and substance/secondary extensions; distinct subjects. -/
def split (x s : B) : Prop := (x = 2 ∧ s = 0) ∨ (x = 3 ∧ s = 1)
def creature (x : B) : Prop := x = 2 ∨ x = 3
def noCause : B → B → Unit → Prop := fun _ _ _ => False
def subjectCause (s x : B) (_ : Unit) : Prop := common x s
def splitCause (s x : B) (_ : Unit) : Prop := split x s
abbrev degreeOrder : Preorder (Bool × Bool) :=
  @Prod.instPreorder Bool Bool TruthCore.Models.Order.boolOrder TruthCore.Models.Order.boolOrder
instance degreeLE : DecidableRel degreeOrder.le := fun a b =>
  inferInstanceAs (Decidable ((a.1 = false ∨ b.1 = true) ∧ (a.2 = false ∨ b.2 = true)))

/-- A product order permits two actually reached incomparable degrees. -/
def partialNear (x : B) : Bool × Bool := if x = 2 then (true, false) else (false, true)
def totalNear : B → Nat
  | .subject0 => 0 | .subject1 => 1 | .accident0 => 2 | .accident1 => 3
def totalMore (_ : Unit) (x y : B) : Prop := totalNear y < totalNear x
def noMore : Unit → B → B → Prop := fun _ _ _ => False
end Control

/-- One joint finite control certificate. Each row fixes carrier, world,
substance, existence, subjects and secondary extensions unless its changed
parameter is explicitly named. It does not assert full BEING_4 compatibility. -/
def Controls : Prop :=
  SubjectFocalReading Control.existsAt Control.substance Control.common ∧
  (Account Control.substance Control.common .primary 0 ∧
    ¬ Account Control.substance Control.common .secondary 0) ∧
  (Account Control.substance Control.common .secondary 2 ∧
    ¬ Account Control.substance Control.common .primary 2) ∧
  CommonCenter Control.substance Control.common 0 ∧
  (∃ s, Control.substance s ∧ s ≠ (0 : Control.B)) ∧
  CreatureSubjectBridge Control.substance Control.common Control.creature ∧
  ¬ SubjectCauseBridge Control.common Control.noCause ∧
  ¬ OrderedToPrimaryAsCauseReading (HasBeing Control.substance Control.common)
      Control.noCause Control.creature () 0 ∧
  SubjectCauseBridge Control.common Control.subjectCause ∧
  OrderedToPrimaryAsCauseReading (HasBeing Control.substance Control.common)
      Control.subjectCause Control.creature () 0 ∧
  ¬ @DegreeComparable Control.B (Bool × Bool) Control.degreeOrder Control.partialNear ∧
  DegreeComparable Control.totalNear ∧
  Calibration Control.totalMore Control.totalNear ∧
  ¬ Calibration Control.noMore Control.totalNear ∧
  ApproachToPrimaryReading (HasBeing Control.substance Control.common)
      Control.totalMore () Control.totalNear 0 ∧
  ¬ ApproachToPrimaryReading (HasBeing Control.substance Control.common)
      Control.noMore () Control.totalNear 0 ∧
  SubjectFocalReading Control.existsAt Control.substance Control.split ∧
  (¬ ∃ p, CommonCenter Control.substance Control.split p) ∧
  CreatureSubjectBridge Control.substance Control.split Control.creature ∧
  SubjectCauseBridge Control.split Control.splitCause ∧
  ¬ OrderedToPrimaryAsCauseReading (HasBeing Control.substance Control.split)
      Control.splitCause Control.creature () 0 ∧
  ¬ OrderedToPrimaryAsCauseReading (HasBeing Control.substance Control.common)
      Control.subjectCause (fun _ => True) () 0 ∧
  (∀ p, CommonCenter Control.substance Control.common p ↔ p = 0) ∧
  ¬ CreatureSubjectBridge Control.substance Control.common (fun _ => True)

/-- Generic substantive consequence of the candidate body: the populated
secondary account cannot have the same extension as the primary account. -/
def RoleDiversity : Prop :=
  ∀ (B : Type) (E S : B → Prop) (I : B → B → Prop),
    SubjectFocalReading E S I →
    (∀ x, Secondary S I x → ¬ S x) ∧
    (∃ x, Account S I .primary x ∧ ¬ Account S I .secondary x) ∧
    ∃ x, Account S I .secondary x ∧ ¬ Account S I .primary x
end TruthCore.Causality.SubjectFocalRoles
