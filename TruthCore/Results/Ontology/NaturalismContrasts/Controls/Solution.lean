module

public import TruthCore.Ontology.NaturalismContrasts
public import TruthCore.Results.Ontology.NaturalismContrasts.Exclusion.Solution

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismContrasts.Controls

open TruthCore.Ontology.NaturalismContrasts TruthCore.Ontology.Naturalism TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Case.Catholicism (RemoteFromAll IsSimple)

inductive Candidate | whole | part | absent

/-- Explicit constructors keep these model predicates free of overlap-generated
propositional extensionality. The absent candidate never exists. -/
def one : Candidate → Prop := Candidate.rec (motive := fun _ => Prop) True False False
def two : Candidate → Prop := Candidate.rec (motive := fun _ => Prop) True True False
def partOnly : Candidate → Prop := Candidate.rec (motive := fun _ => Prop) False True False

def component (x y : Candidate) : Prop := x = .part ∧ y = .whole
def samePart (x y : Candidate) : Prop := x = y
def pairPart (x y : Candidate) : Prop := x = y ∨ component x y
def noComponent (_ _ : Candidate) : Prop := False
def wholeComposite (x : Candidate) : Prop := x = .whole
def noComposite (_ : Candidate) : Prop := False

/-- The unused causal field is empty. No causal-worldview claim is made. -/
def ontic (population : Candidate → Prop) : Ontic Unit Candidate where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ => population
  Causes := fun _ _ _ => False

/-- The one region may represent the entire spacetime region; occupation here
needs no external surrounding space. No geometry or extent is inferred. -/
def spacetime (parts : Candidate → Candidate → Prop) (location : Candidate → Prop) :
    Frame Candidate where
  Region := Unit
  locatedAt := fun x _ => location x
  related := fun x y => x = y
  partOf := parts
  whole := .whole

def scenario (population : Candidate → Prop) (parts : Candidate → Candidate → Prop)
    (location : Candidate → Prop) (components : Candidate → Candidate → Prop)
    (composites : Candidate → Prop) : Scenario where
  World := Unit
  Being := Candidate
  o := ontic population
  F := spacetime parts location
  ComponentOf := components
  Composite := composites
  w := ()

def populated : Scenario := scenario two pairPart two component wholeComposite
def soleWhole : Scenario := scenario one samePart one noComponent noComposite
def noCompositeBridge : Scenario := scenario two pairPart two component noComposite
def noPartBridge : Scenario := scenario two pairPart two noComponent noComposite
def noPartNaturalism : Scenario := scenario two samePart two noComponent noComposite
def absentWhole : Scenario := scenario partOnly samePart partOnly noComponent noComposite

theorem twoExist (parts : Candidate → Candidate → Prop) (location : Candidate → Prop)
    (components : Candidate → Candidate → Prop) (composites : Candidate → Prop) :
    TwoExist (scenario two parts location components composites).o () :=
  ⟨.whole, .part, trivial, trivial, fun h => Candidate.noConfusion h⟩

theorem pairN1 :
    ExistenceNaturalism (ontic two) (PartOfSpacetime (spacetime pairPart two)) () := by
  intro x hx
  cases x with
  | whole => exact Or.inl rfl
  | part => exact Or.inr ⟨rfl, rfl⟩
  | absent => exact False.elim hx

theorem pairParts :
    ExistingProperPartsAreComponents (ontic two) (spacetime pairPart two) component () := by
  intro x hx _ hProper
  cases x with
  | whole => exact False.elim (hProper rfl)
  | part => exact ⟨rfl, rfl⟩
  | absent => exact False.elim hx

theorem emptyComponents (population : Candidate → Prop)
    (parts : Candidate → Candidate → Prop) (location composites : Candidate → Prop) :
    ExistingComponentsMakeWholeComposite (ontic population) (spacetime parts location)
      noComponent composites () := fun _ _ h _ => False.elim h

theorem identityParts (population location : Candidate → Prop) :
    ExistingProperPartsAreComponents (ontic population) (spacetime samePart location)
      noComponent () := fun _ _ hPart hProper => False.elim (hProper hPart)

theorem locatedN1 (population : Candidate → Prop) (parts : Candidate → Candidate → Prop) :
    ExistenceNaturalism (ontic population) (Located (spacetime parts population)) () :=
  fun _ h => ⟨(), h⟩

theorem wholeRemoteFromComponent : RemoteFromAll component Candidate.whole := by
  rintro x ⟨hPart, _⟩
  exact Candidate.noConfusion hPart

theorem wholeSimpleRemote :
    ExistingSimpleRemote (ontic two) component noComposite () :=
  ⟨.whole, trivial, id, wholeRemoteFromComponent⟩

theorem noLinksWholeRemote (population : Candidate → Prop)
    (hWhole : population .whole) :
    ExistingSimpleRemote (ontic population) noComponent noComposite () :=
  ⟨.whole, hWhole, id, fun _ => id⟩

theorem notTwoSole : ¬ TwoExist soleWhole.o soleWhole.w := by
  rintro ⟨x, y, hx, hy, hDistinct⟩
  cases x <;> cases y <;> first
    | exact hDistinct rfl
    | exact False.elim hx
    | exact False.elim hy

theorem contrastControls : ContrastControls := by
  have hFull : PartBackground populated :=
    ⟨pairN1, pairParts,
      (fun _ _ _ _ => rfl), twoExist pairPart two component wholeComposite⟩
  refine ⟨⟨populated, hFull, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact Exclusion.noExistingSimpleRemote populated.o populated.F
      populated.ComponentOf populated.Composite populated.w hFull.1 hFull.2.1 hFull.2.2.1 hFull.2.2.2
  · refine ⟨soleWhole, ?_, identityParts one one, emptyComponents one samePart one noComposite,
      notTwoSole, noLinksWholeRemote one trivial, trivial, ⟨(), trivial⟩, rfl,
      locatedN1 one samePart⟩
    intro x hx
    cases x with
    | whole => rfl
    | part => exact False.elim hx
    | absent => exact False.elim hx
  · refine ⟨noCompositeBridge, pairN1, pairParts,
      ?_, twoExist pairPart two component noComposite, wholeSimpleRemote⟩
    intro hBridge
    exact hBridge .part trivial ⟨rfl, rfl⟩ (fun h => Candidate.noConfusion h)
  · refine ⟨noPartBridge, pairN1, ?_,
      emptyComponents two pairPart two noComposite,
      twoExist pairPart two noComponent noComposite, noLinksWholeRemote two trivial⟩
    intro hBridge
    exact hBridge .part trivial (Or.inr ⟨rfl, rfl⟩) (fun h => Candidate.noConfusion h)
  · refine ⟨noPartNaturalism, ?_, locatedN1 two samePart,
      identityParts two two, emptyComponents two samePart two noComposite,
      twoExist samePart two noComponent noComposite,
      ⟨.part, trivial, id, fun _ => id⟩⟩
    intro hN1
    exact Candidate.noConfusion (hN1 .part trivial)
  · refine ⟨absentWhole, locatedN1 partOnly samePart, ?_, id,
      .part, trivial, (fun h => Candidate.noConfusion h), ⟨(), trivial⟩⟩
    rintro ⟨r, h⟩
    exact h

end TruthCore.Results.Ontology.NaturalismContrasts.Controls
