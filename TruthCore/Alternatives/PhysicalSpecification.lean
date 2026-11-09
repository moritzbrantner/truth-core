module

public import Mathlib.ModelTheory.Semantics

/-!
# Explicit specification interpretations for the physical-ground comparison

Reuse Mathlib's full first-order syntax and satisfaction, as ReferenceAnchor
does. No finite-domain, bounded-formula-search or physical composition restriction
is built into either sense. Both are analyst interpretations, not completion of
the original Papineau sense. Ordinary-symbol calibration remains OPEN.
-/

@[expose] public section
namespace TruthCore.Alternatives.PhysicalSpecification
open FirstOrder

/-- Which function/relation symbols are outside the special vocabulary is an
explicit interpretation input. It is not a free flag for specifiability of an
object. Calibration must reject predicates or operations disguising names. -/
structure Vocabulary (L : Language) where
  ordinaryFunction : ∀ n, L.Functions n → Prop
  ordinaryRelation : ∀ n, L.Relations n → Prop

/-- The permitted sublanguage. No individual constants (arity zero functions)
are admitted, even if classified ordinary. Positive-arity functions and all
relation arities remain available. Mathlib types enforce arity and variable scope. -/
def ordinaryLanguage {L : Language} (v : Vocabulary L) : Language where
  Functions n := {f : L.Functions n // v.ordinaryFunction n f ∧ 0 < n}
  Relations n := {r : L.Relations n // v.ordinaryRelation n r}

/-- PHYSICAL_OF_A_GROUND_3: a name-free definite description at ONE supplied
interpretation. The only free variable is the object variable; there are no
individual constants or free parameters. Quantifiers range over the whole D.
An admitted predicate could still disguise a name: calibration is not a theorem. -/
def Naming {L : Language} (v : Vocabulary L) {D : Type}
    (i : (ordinaryLanguage v).Structure D) (x : D) : Prop :=
  ∃ p : (ordinaryLanguage v).Formula Unit,
    ∀ y, @Language.Formula.Realize _ D i Unit p (fun _ => y) ↔ y = x

/-- Parameter symbols and their values are explicit; they are not additional
individual constants hidden in the ordinary signature. -/
structure Interpretation {L : Language} (v : Vocabulary L) (P D : Type) where
  model : (ordinaryLanguage v).Structure D
  parameter : P → D

/-- PHYSICAL_OF_A_GROUND_4: ONE formula defines a unary target across EVERY
admitted interpretation on an arbitrary fixed full carrier. Only permitted
parameters can occur in its syntax; values are supplied by each interpretation.
A nonempty interpretation class is required. This does not assert adequacy of
that class, transport of the target, or coverage of varying-carrier semantics. -/
def Definability {L : Language} (v : Vocabulary L) {P D : Type}
    (permitted : P → Prop) (admitted : Interpretation v P D → Prop)
    (target : Interpretation v P D → D → Prop) : Prop :=
  (∃ i, admitted i) ∧ ∃ p : (ordinaryLanguage v).Formula (Unit ⊕ {a // permitted a}),
    ∀ i, admitted i → ∀ x,
      @Language.Formula.Realize _ D i.model _ p
        (Sum.elim (fun _ => x) (fun a => i.parameter a.val)) ↔ target i x

/-! ## Explicit Bool controls, never a proposed complete physical language -/
inductive Marker : Nat → Type where
  | marked : Marker 1

def controlSignature : Language := ⟨fun _ => Empty, Marker⟩
def controlVocabulary : Vocabulary controlSignature :=
  ⟨fun _ e => Empty.elim e, fun _ _ => True⟩

@[instance_reducible] def controlOriginal : (ordinaryLanguage controlVocabulary).Structure Bool where
  funMap := fun f _ => Empty.elim f.val
  RelMap := fun r xs => match r.val with | .marked => xs 0 = true

def swap : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩

@[instance_reducible] def controlTransported :
    (ordinaryLanguage controlVocabulary).Structure Bool :=
  @Equiv.inducedStructure _ Bool Bool controlOriginal swap

def markedFormula : (ordinaryLanguage controlVocabulary).Formula Unit :=
  Language.Relations.formula (⟨Marker.marked, trivial⟩) (fun _ => .var ())

def namingControl : Prop := Naming controlVocabulary controlOriginal true

def partFreeControl : Prop :=
  Naming controlVocabulary controlOriginal true ∧ ¬ (fun _ : Bool => False) true

def uniformControl : Prop := Definability controlVocabulary (fun _ : Empty => False)
  (fun _ : Interpretation controlVocabulary Empty Bool => True) (fun _ x => x = true)

def noUniformControl : Prop := ¬ uniformControl

def permittedControl : Prop := Definability controlVocabulary (fun _ : Unit => True)
  (fun _ : Interpretation controlVocabulary Unit Bool => True) (fun i x => x = i.parameter ())

/-- There is no syntax variable for a forbidden parameter, since the parameter
part of the free-variable type is the empty subtype. No global undefinability
claim is made by this type-level permission control. -/
def forbiddenControl : Prop := ¬ ∃ _ : {_u : Unit // False}, True

end TruthCore.Alternatives.PhysicalSpecification
