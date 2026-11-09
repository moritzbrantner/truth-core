module
public import TruthCore.Alternatives.PhysicalSpecification

/-!
Restricted richer-language candidate: first-order formulas, Boolean connectives,
and reflexive finite reachability along an admitted ordinary binary relation.
No object names, new predicate interpretations, or interpretation-dependent syntax
are added. Reachability is graph-theoretic, not a causal or bearer relation.
This candidate does not complete PHYSICAL_OF_A_GROUND_2.
-/
@[expose] public section
namespace TruthCore.Alternatives.PhysicalSpecification
open FirstOrder

/-- A finite path, including the zero-edge path. No bound on path length. -/
inductive Path {D : Type} (r : D → D → Prop) : D → D → Prop where
  | refl (x) : Path r x x
  | step {x y z} : r x y → Path r y z → Path r x z

/-- A deliberately restricted FO+reachability language. Endpoints are free
variables only. Parameters must already belong to the permitted subtype.
No quantification over predicates, arbitrary semantic atoms or new constants. -/
inductive PathFormula {L : Language} (v : Vocabulary L) (A : Type) where
  | firstOrder : (ordinaryLanguage v).Formula A → PathFormula v A
  | neg : PathFormula v A → PathFormula v A
  | conj : PathFormula v A → PathFormula v A → PathFormula v A
  | reach : (ordinaryLanguage v).Relations 2 → A → A → PathFormula v A

/-- Full carrier satisfaction; reach uses the same model as the FO fragment. -/
def PathFormula.realize {L : Language} {v : Vocabulary L} {A D : Type}
    (i : (ordinaryLanguage v).Structure D) (a : A → D) : PathFormula v A → Prop
  | .firstOrder p => @Language.Formula.Realize _ D i _ p a
  | .neg p => ¬ p.realize i a
  | .conj p q => p.realize i a ∧ q.realize i a
  | .reach r x y => Path (fun u w => i.RelMap r (fun k => if k = 0 then u else w)) (a x) (a y)

/-- Indexed domains really may differ. One syntax object is selected before
all indices; the target is a family, not a predicate on an implicit common D.
Nonemptiness excludes the empty admitted-class shortcut. -/
def VaryingPathDefinability {L : Language} (v : Vocabulary L) {P I : Type}
    (D : I → Type) (model : ∀ i, Interpretation v P (D i))
    (permitted : P → Prop) (admitted : I → Prop) (target : ∀ i, D i → Prop) : Prop :=
  (∃ i, admitted i) ∧ ∃ p : PathFormula v (Unit ⊕ {a // permitted a}),
    ∀ i, admitted i → ∀ x, p.realize (model i).model
      (Sum.elim (fun _ => x) (fun a => (model i).parameter a.val)) ↔ target i x

/-- FO alternative on precisely the same indexed profile and parameter policy. -/
def VaryingFirstOrderDefinability {L : Language} (v : Vocabulary L) {P I : Type}
    (D : I → Type) (model : ∀ i, Interpretation v P (D i))
    (permitted : P → Prop) (admitted : I → Prop) (target : ∀ i, D i → Prop) : Prop :=
  (∃ i, admitted i) ∧ ∃ p : (ordinaryLanguage v).Formula (Unit ⊕ {a // permitted a}),
    ∀ i, admitted i → ∀ x, @Language.Formula.Realize _ (D i) (model i).model _ p
      (Sum.elim (fun _ => x) (fun a => (model i).parameter a.val)) ↔ target i x

/-- Cross-domain comparison is a supplied relation, never implicit identity.
Partial/many-to-many relations are allowed; totality or adequacy is NOT asserted. -/
def Corresponds {I : Type} {D : I → Type} (c : ∀ i j, D i → D j → Prop)
    (target : ∀ i, D i → Prop) : Prop :=
  ∀ i j x y, c i j x y → (target i x ↔ target j y)

/-- Registered comparison: FO embeds on an identical profile. -/
def embeddingControl : Prop := ∀ (L : Language.{0, 0}) (v : Vocabulary L) (P I : Type)
    (D : I → Type) (m : ∀ i, Interpretation v P (D i)) (p : P → Prop)
    (a : I → Prop) (t : ∀ i, D i → Prop),
    VaryingFirstOrderDefinability v D m p a t → VaryingPathDefinability v D m p a t

/-- The prior fixed-carrier candidate is exactly the constant-carrier FO case
indexed by its interpretations, with the very same admitted class and target. -/
def specializationControl : Prop := ∀ (L : Language.{0, 0}) (v : Vocabulary L) (P D : Type)
    (p : P → Prop) (a : Interpretation v P D → Prop) (t : Interpretation v P D → D → Prop),
    Definability v p a t ↔
      VaryingFirstOrderDefinability v (fun _ : Interpretation v P D => D) (fun i => i) p a t

/-- Two edges suffice for reachability; an edgeless graph cannot connect distinct
vertices. This distinguishes reachability from a single edge and from a free flag. -/
def pathControl : Prop :=
  Path (fun x y : Nat => y = x + 1) 0 2 ∧
  ¬ (fun x y : Nat => y = x + 1) 0 2 ∧ ¬ Path (fun _ _ : Bool => False) false true

/-- Two actual carrier types, with one explicitly permitted anchor. No symbol
names every object. The marker is constantly false in both interpretations. -/
def sampleDomain : Bool → Type | false => Unit | true => Bool

def sampleAnchor : (b : Bool) → sampleDomain b | false => () | true => false

@[instance_reducible] def sampleModel (b : Bool) :
    Interpretation controlVocabulary Unit (sampleDomain b) where
  model := { funMap := fun f _ => Empty.elim f.val, RelMap := fun _ _ => False }
  parameter := fun _ => sampleAnchor b

/-- Genuine varying-carrier nonvacuity: equality to the sole permitted anchor
works on Unit AND Bool, under the same marker calibration and same formula. -/
def varyingControl : Prop := VaryingPathDefinability controlVocabulary sampleDomain
  sampleModel (fun _ : Unit => True) (fun _ => True) (fun b x => x = sampleAnchor b)

/-- Comparing only anchor-to-anchor and nonanchor-to-nonanchor pairs preserves
this particular target. The relation is explicit and need not be a bijection. -/
def sampleCorrespondence (b c : Bool) (x : sampleDomain b) (y : sampleDomain c) : Prop :=
  (x = sampleAnchor b ∧ y = sampleAnchor c) ∨ (x ≠ sampleAnchor b ∧ y ≠ sampleAnchor c)

def correspondenceControl : Prop := Corresponds sampleCorrespondence (fun b x => x = sampleAnchor b)

inductive Link : Nat → Type where | edge : Link 2

def linkSignature : Language := ⟨fun _ => Empty, Link⟩
def linkVocabulary : Vocabulary linkSignature := ⟨fun _ e => Empty.elim e, fun _ _ => True⟩
@[reducible] def reachDomain : Bool → Type | false => Nat | true => Bool
def reachAnchor : (b : Bool) → reachDomain b | false => 0 | true => false
/-- Ordinary graph adjacency, not an outcome-coded target predicate:
Nat successor and Bool inequality. Neither uses a physical or intellect label. -/
def adjacency : (b : Bool) → reachDomain b → reachDomain b → Prop
  | false, x, y => y = x + 1
  | true, x, y => x ≠ y

@[instance_reducible] def reachModel (b : Bool) :
    Interpretation linkVocabulary Unit (reachDomain b) where
  model := {
    funMap := fun f _ => Empty.elim f.val
    RelMap := fun r xs => match r.val with | .edge => adjacency b (xs 0) (xs 1) }
  parameter := fun _ => reachAnchor b

/-- A single reachability formula covers the full Nat and Bool domains from
one permitted anchor. Rich syntax is actually used; no FO undefinability claim. -/
def reachVaryingControl : Prop := VaryingPathDefinability linkVocabulary reachDomain
  reachModel (fun _ : Unit => True) (fun _ => True) (fun _ _ => True)

/-- Root-route diagnostic only: specification by this graph language coexists
with an independently empty composition and intellect assignment. Without a
calibration/bearer bridge it cannot refute the original Aquinas route step. -/
def rootIndependenceControl : Prop := reachVaryingControl ∧
  ¬ (fun _ : reachDomain false => False) (reachAnchor false) ∧
  ¬ (fun _ : reachDomain false => False) (reachAnchor false)

/-- Same sample target, incompatible comparison relation: indiscriminate pairing
identifies a Bool anchor and nonanchor. Correspondence must not be inferred. -/
def correspondenceFailureControl : Prop :=
  ¬ Corresponds (fun (i j : Bool) (_ : sampleDomain i) (_ : sampleDomain j) => True)
    (fun b x => x = sampleAnchor b)

end TruthCore.Alternatives.PhysicalSpecification
