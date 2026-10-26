import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill

/-!
ST I q.14 a.1 co., materialized as AQUINAS-ST-I-Q14-A1. This interface models
aptitude to have another thing's form, not an event of receiving information.
It deliberately does not identify absence of material reception with the
existing highest-immateriality antecedent, or cognition with intellect.

The q.75 interface concerns a human intellectual principle's range of bodily
natures and constitutive interference. Its CanUnderstand relation has neither
reception modes nor a divine interpretation; no meaning-preserving reuse of
that relation supplies the distinctions needed here. Divine knowledge is not
being modeled as passive acquisition from creatures (q.14 a.1 ad 1–3).
-/
namespace TruthCore.Latin.Aquinas.SummaTheologiae.FormReception

/-- Modes of the capacity to have a form; neither constructor asserts an
actual reception event. Sense already has the without-matter mode. -/
inductive Mode where
  | withMatter
  | withoutMatter

/-- ForeignForm x f says f is a form of something other than x. This does not
say f differs in species from x's own form. Form ranges over possible objects
of the capacity; no actual external object is asserted to exist. Cognitive,
sensory and intellectual capacities remain distinct primitive predicates. -/
structure Model (Being Form : Type) where
  ForeignForm : Being → Form → Prop
  CanHaveForm : Being → Form → Mode → Prop
  Cognitive : Being → Prop
  Sensory : Being → Prop
  Intellectual : Being → Prop

/-- Aptitude for another's form, without specifying its mode. -/
def ForeignFormCapacity {Being Form : Type} (m : Model Being Form) (x : Being) : Prop :=
  ∃ f, m.ForeignForm x f ∧ ∃ mode, m.CanHaveForm x f mode

/-- Aptitude for another's form without matter. This includes sensory
receptivity and therefore is not a definition of intellect. -/
def WithoutMatterCapacity {Being Form : Type} (m : Model Being Form) (x : Being) : Prop :=
  ∃ f, m.ForeignForm x f ∧ m.CanHaveForm x f .withoutMatter

/-- A negative restriction on reception modes. It neither asserts any capacity
nor translates the component-free immateriality of IntellectWill.lean. -/
def NoMaterialReception {Being Form : Type} (m : Model Being Form) (x : Being) : Prop :=
  ∀ f, ¬ m.CanHaveForm x f .withMatter

/-- q.14 a.1 co., cognoscens natum est habere formam etiam rei alterius.
A cognitive thing has aptitude for another thing's form. No converse, actual
acquisition, or universal knowledge is asserted. -/
def CognitiveAptitudeReading {Being Form : Type} (m : Model Being Form) : Prop :=
  ∀ x, m.Cognitive x → ForeignFormCapacity m x

/-- q.14 a.1 co., sensus ... receptivus est specierum sine materia.
Sense has without-matter receptivity. This does not equate sense and intellect. -/
def SenseReceptivityReading {Being Form : Type} (m : Model Being Form) : Prop :=
  ∀ x, m.Sensory x → WithoutMatterCapacity m x

/-- With positive availability, excluding the material mode leaves the
without-matter mode. Availability is an explicit hypothesis, not a definition
of immateriality or a new source-attributed universal premise. -/
theorem availableFormWithoutMatter {Being Form : Type} (m : Model Being Form) (x : Being)
    (hAvailable : ForeignFormCapacity m x) (hNoMatter : NoMaterialReception m x) :
    WithoutMatterCapacity m x := by
  obtain ⟨f, hf, mode, hm⟩ := hAvailable
  cases mode with
  | withMatter => exact False.elim (hNoMatter f hm)
  | withoutMatter => exact ⟨f, hf, hm⟩

/-- Omission control: an empty capacity relation has no material reception
but also no foreign-form aptitude. Both source readings remain satisfied. -/
def emptyRecipient : Model Unit Unit where
  ForeignForm := fun _ _ => True
  CanHaveForm := fun _ _ _ => False
  Cognitive := fun _ => False
  Sensory := fun _ => False
  Intellectual := fun _ => False

theorem availabilityOmission :
    CognitiveAptitudeReading emptyRecipient ∧ SenseReceptivityReading emptyRecipient ∧
    NoMaterialReception emptyRecipient () ∧ ¬ ForeignFormCapacity emptyRecipient () := by
  refine ⟨fun _ h => False.elim h, fun _ h => False.elim h, fun _ h => h, ?_⟩
  rintro ⟨_, _, _, h⟩
  exact h

/-- Omission control: without-matter sensory aptitude does not by itself
supply intellectual aptitude. The predicates are intentionally not identified. -/
def sensoryRecipient : Model Unit Unit where
  ForeignForm := fun _ _ => True
  CanHaveForm := fun _ _ mode => mode = .withoutMatter
  Cognitive := fun _ => True
  Sensory := fun _ => True
  Intellectual := fun _ => False

theorem intellectualGradeOmission :
    CognitiveAptitudeReading sensoryRecipient ∧ SenseReceptivityReading sensoryRecipient ∧
    NoMaterialReception sensoryRecipient () ∧ WithoutMatterCapacity sensoryRecipient () ∧
    ¬ sensoryRecipient.Intellectual () := by
  exact ⟨fun _ _ => ⟨(), True.intro, .withoutMatter, rfl⟩,
    fun _ _ => ⟨(), True.intro, rfl⟩, fun _ h => Mode.noConfusion h,
    ⟨(), True.intro, rfl⟩, fun h => h⟩

/-- Even attaching the old structural antecedent to the empty recipient
cannot derive the primitive intellectual predicate from these source readings.
This is a formal omission schema, not a metaphysically possible being. -/
theorem oldTargetOmission :
    ¬ ImmaterialIsIntellectualReading (fun _ : Unit => False)
      emptyRecipient.Intellectual (fun _ _ => False) := by
  intro h
  exact h () (fun hf => hf) (fun _ hf => hf)

end TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
