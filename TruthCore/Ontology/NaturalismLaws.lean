module

public import TruthCore.Ontology.Naturalism
public import TruthCore.Modern.Hume.Regularity

/-! Analyst representation test for #1109. A rule index is not an existing
entity merely because it is in the type of rules. `Sum.inl` represents bearers;
`Sum.inr` represents candidate law entities. This chosen disjoint representation
prevents two rule indices from silently denoting the same entity. It is not a
complete law ontology, a best-system selector, or a theory of powers. -/

@[expose] public section
namespace TruthCore.Ontology.NaturalismLaws
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism

/-- `instantiates l b` means bearer b instantiates the universal represented by l,
not that b is a proof or a sentence asserting l. Existing instantiation also
requires bearer presence. `bearerAt` is occupation, not causal influence. The
presence of a law entity is independent of both its instances and rule truth. -/
structure Representation (W B R : Type) where
  Region : Type
  bearerPresent : W → B → Prop
  lawPresent : W → R → Prop
  bearerAt : B → Region → Prop
  instantiates : R → B → Prop
  whole : B

variable {W B R : Type}

def ontic (m : Representation W B R) : Ontic W (B ⊕ R) where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => match x with
    | .inl b => m.bearerPresent w b
    | .inr l => m.lawPresent w l
  Causes := fun _ _ _ => False

/-- A supplied law-location criterion; no instance support is assumed. Empty
related/partOf fields are bookkeeping outside this occupant-only comparison. -/
def frame (m : Representation W B R) (lawAt : R → m.Region → Prop) : Frame (B ⊕ R) where
  Region := m.Region
  locatedAt := fun x r => match x with
    | .inl b => m.bearerAt b r
    | .inr l => lawAt l r
  related := fun _ _ => False
  partOf := fun _ _ => False
  whole := .inl m.whole

def ActualInstance (m : Representation W B R) (w : W) (l : R) : Prop :=
  ∃ b, m.bearerPresent w b ∧ m.instantiates l b

/-- Immanent location: the representative occupies a region precisely through
an existing instance occupying it. The reverse direction is substantive; it is
not licensed by merely allowing instances to confer location. Region geometry,
causal laws and metaphysical applicability remain independent open inputs. -/
def immanentAt (m : Representation W B R) (w : W) (l : R) (r : m.Region) : Prop :=
  ∃ b, m.bearerPresent w b ∧ m.instantiates l b ∧ m.bearerAt b r

def InstanceConfersLocation (m : Representation W B R) (w : W)
    (lawAt : R → m.Region → Prop) : Prop :=
  ∀ l b r, m.bearerPresent w b → m.instantiates l b → m.bearerAt b r → lawAt l r

def LocationHasInstanceSupport (m : Representation W B R) (w : W)
    (lawAt : R → m.Region → Prop) : Prop :=
  ∀ l r, lawAt l r → ∃ b, m.bearerPresent w b ∧ m.instantiates l b ∧ m.bearerAt b r

def ExistingLawsInstantiated (m : Representation W B R) (w : W) : Prop :=
  ∀ l, m.lawPresent w l → ActualInstance m w l

/-- The weaker forward bridge follows from the concrete immanent criterion;
the controls below show that this implication cannot be reversed. -/
theorem immanent_confers (m : Representation W B R) (w : W) :
    InstanceConfersLocation m w (immanentAt m w) :=
  fun _ b _ hb hi hat => ⟨b, hb, hi, hat⟩


open TruthCore.Modern.Hume.Regularity

/-- Three separate representations, not a joint worldview. Selected-rule
truth is the existing finite-language diagnostic, not a full Lewis theory.
The last row exports both location criteria: the weak frame is populated with
an uninstantiated law, whereas the immanent frame leaves that law unlocated. -/
def Controls : Prop :=
  BestSystemTest ∧
  (∃ m : Representation Unit Bool Regularity,
    ExistenceNaturalism (ontic m) (Located (frame m (immanentAt m ()))) () ∧
    m.lawPresent () .pattern ∧ ActualInstance m () .pattern ∧
    ¬ m.lawPresent () .incidental) ∧
  (∃ m : Representation Unit Bool Regularity,
    ExistenceNaturalism (ontic m) (Located (frame m (immanentAt m ()))) () ∧
    (∀ l, ¬ m.lawPresent () l) ∧
    (∃ b, m.bearerPresent () b) ∧ ¬ ActualInstance m () .pattern) ∧
  (∃ (m : Representation Unit Bool Regularity) (lawAt : Regularity → m.Region → Prop),
    ExistenceNaturalism (ontic m) (Located (frame m lawAt)) () ∧
    InstanceConfersLocation m () lawAt ∧ ¬ LocationHasInstanceSupport m () lawAt ∧
    m.lawPresent () .pattern ∧ ¬ ActualInstance m () .pattern ∧
    ¬ Located (frame m (immanentAt m ())) (.inr .pattern) ∧
    ∃ b, m.bearerPresent () b ∧ Located (frame m lawAt) (.inl b))

end TruthCore.Ontology.NaturalismLaws
