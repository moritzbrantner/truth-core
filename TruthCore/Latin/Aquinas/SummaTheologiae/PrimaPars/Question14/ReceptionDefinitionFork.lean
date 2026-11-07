module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.Article1
public import TruthCore.Logic.ExcludedMiddle

/-! Analyst comparison of three operational proxies on one admitted scope.
These are OPEN calibrations to the existing Intellectual predicate, not three
adequate or exhaustive theories of intellect. Source sense/grade and aptitude
remain distinct. Actual input causation, semantic understanding and divine
passive acquisition are NOT inferred from the state-change proxy below. -/

@[expose] public section
namespace TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork
open FormReception

/-- Occurring foreign-form state-change data. No causal production or reception
capacity is built in. The relation is an operational PROXY, not a definition of
information acquisition or intellect. The before/after states can coincide. -/
structure ChangeProfile (Being Form Event State : Type) where
  Occurs : Event → Prop
  receiver : Event → Being
  form : Event → Form
  before : Event → State
  after : Event → State

/-- An occurring state change carrying a form foreign to the chosen receiver.
It supplies neither CanHaveForm nor intellectual grade. -/
def ForeignFormChange {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (x : B) : Prop :=
  ∃ e, a.Occurs e ∧ a.receiver e = x ∧ m.ForeignForm x (a.form e) ∧
    a.before e ≠ a.after e

/-- OPEN scope-relative identification, not a source attribution. -/
def CapacityCalibration {B F : Type} (m : Model B F) (scope : B → Prop) : Prop :=
  ∀ x, scope x → (m.Intellectual x ↔ ForeignFormCapacity m x)

def WithoutMatterCalibration {B F : Type} (m : Model B F) (scope : B → Prop) : Prop :=
  ∀ x, scope x → (m.Intellectual x ↔ WithoutMatterCapacity m x)

/-- OPEN identification with the operational state-change PROXY, not with a
complete input-causation account. Rejecting it does not refute such accounts. -/
def ChangeProxyCalibration {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (scope : B → Prop) : Prop :=
  ∀ x, scope x → (m.Intellectual x ↔ ForeignFormChange m a x)

/-- OPEN named menu: at least one calibration holds for this SAME dictionary
and scope. The proposals can overlap. No philosophical completeness follows. -/
def NamedMenu {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (scope : B → Prop) : Prop :=
  CapacityCalibration m scope ∨ WithoutMatterCalibration m scope ∨
    ChangeProxyCalibration m a scope

/-- Precise remaining extension on the same supplied scope. -/
def Remaining {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (scope : B → Prop) : Prop :=
  ¬ CapacityCalibration m scope ∧ ¬ WithoutMatterCalibration m scope ∧
    ¬ ChangeProxyCalibration m a scope

def CapacityCalibrationFails {B F : Type} (m : Model B F) (scope : B → Prop) : Prop :=
  ¬ CapacityCalibration m scope

def WithoutMatterCalibrationFails {B F : Type} (m : Model B F) (scope : B → Prop) : Prop :=
  ¬ WithoutMatterCalibration m scope

def DefinitionFork {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (scope : B → Prop) : Prop :=
  NamedMenu m a scope ∨ Remaining m a scope

/-- The comparison scope must cover EVERY receiver in the old structural
antecedent. It cannot silently discard the difficult old-target cases. -/
def StructuralScopeCovered {B : Type} (scope matterForm : B → Prop)
    (component : B → B → Prop) : Prop :=
  ∀ x, ¬ matterForm x → (∀ y, ¬ component x y) → scope x

def StructuralCapacityAvailable {B F : Type} (m : Model B F)
    (matterForm : B → Prop) (component : B → B → Prop) : Prop :=
  ∀ x, ¬ matterForm x → (∀ y, ¬ component x y) → ForeignFormCapacity m x

def StructuralMaterialModeExcluded {B F : Type} (m : Model B F)
    (matterForm : B → Prop) (component : B → B → Prop) : Prop :=
  ∀ x, ¬ matterForm x → (∀ y, ¬ component x y) → NoMaterialReception m x

/-- Separate actual-change availability required ONLY by the proxy branch.
No such event is derived from structural immateriality or aptitude. -/
def StructuralChangeAvailable {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (matterForm : B → Prop)
    (component : B → B → Prop) : Prop :=
  ∀ x, ¬ matterForm x → (∀ y, ¬ component x y) → ForeignFormChange m a x

/-- A material-only capacity distinguishes the pointwise strength order. -/
def materialRecipient : Model Unit Unit where
  ForeignForm := fun _ _ => True
  CanHaveForm := fun _ _ mode => mode = .withMatter
  Cognitive := fun _ => True
  Sensory := fun _ => False
  Intellectual := fun _ => True

/-- A primitive intellectual receiver with capacity but no assumed event.
This is an API interpretation, not a metaphysically possible divine being. -/
def dormantRecipient : Model Unit Unit :=
  { sensoryRecipient with Sensory := fun _ => False, Intellectual := fun _ => True }

def noChange : ChangeProfile Unit Unit Unit Bool where
  Occurs := fun _ => False
  receiver := fun _ => ()
  form := fun _ => ()
  before := fun _ => false
  after := fun _ => true

def recordedChange : ChangeProfile Unit Unit Unit Bool :=
  { noChange with Occurs := fun _ => True }

/-- Nonempty admitted scope with a positive primitive intellect assignment
outside all three proposed extensions. No preferred winner is selected. -/
def remainingRecipient : Model Bool Unit where
  ForeignForm := fun _ _ => True
  CanHaveForm := fun _ _ _ => False
  Cognitive := fun _ => False
  Sensory := fun _ => False
  Intellectual := fun x => x = false

def remainingChange : ChangeProfile Bool Unit Unit Bool where
  Occurs := fun _ => False
  receiver := fun _ => false
  form := fun _ => ()
  before := fun _ => false
  after := fun _ => true

/-- Separate exact controls. They are not one joint background, a worldview
survey, or real possibilities. The old three omission boundaries are retained
verbatim, including sensory without-matter reception WITHOUT intellect. -/
def Controls : Prop :=
  (CognitiveAptitudeReading emptyRecipient ∧ SenseReceptivityReading emptyRecipient ∧
    NoMaterialReception emptyRecipient () ∧ ¬ ForeignFormCapacity emptyRecipient ()) ∧
  (CognitiveAptitudeReading sensoryRecipient ∧ SenseReceptivityReading sensoryRecipient ∧
    NoMaterialReception sensoryRecipient () ∧ WithoutMatterCapacity sensoryRecipient () ∧
    ¬ sensoryRecipient.Intellectual ()) ∧
  (¬ ImmaterialIsIntellectualReading (fun _ : Unit => False)
    emptyRecipient.Intellectual (fun _ _ => False)) ∧
  (ForeignFormCapacity materialRecipient () ∧ ¬ WithoutMatterCapacity materialRecipient () ∧
    CapacityCalibration materialRecipient (fun _ => True) ∧
    ¬ WithoutMatterCalibration materialRecipient (fun _ => True)) ∧
  (dormantRecipient.Intellectual () ∧ WithoutMatterCapacity dormantRecipient () ∧
    ¬ ForeignFormChange dormantRecipient noChange () ∧
    CapacityCalibration dormantRecipient (fun _ => True) ∧
    WithoutMatterCalibration dormantRecipient (fun _ => True) ∧
    ¬ ChangeProxyCalibration dormantRecipient noChange (fun _ => True) ∧
    StructuralScopeCovered (fun _ : Unit => True) (fun _ => False) (fun _ _ => False) ∧
    StructuralCapacityAvailable dormantRecipient (fun _ => False) (fun _ _ => False) ∧
    StructuralMaterialModeExcluded dormantRecipient (fun _ => False) (fun _ _ => False) ∧
    ImmaterialIsIntellectualReading (fun _ => False) dormantRecipient.Intellectual (fun _ _ => False)) ∧
  (StructuralScopeCovered (fun _ : Unit => True) (fun _ => False) (fun _ _ => False) ∧
    StructuralChangeAvailable dormantRecipient recordedChange (fun _ => False) (fun _ _ => False) ∧
    ChangeProxyCalibration dormantRecipient recordedChange (fun _ => True) ∧
    ImmaterialIsIntellectualReading (fun _ => False) dormantRecipient.Intellectual (fun _ _ => False)) ∧
  (ForeignFormChange emptyRecipient recordedChange () ∧
    ¬ ForeignFormCapacity emptyRecipient ()) ∧
  (Remaining remainingRecipient remainingChange (fun _ => True) ∧
    ¬ NamedMenu remainingRecipient remainingChange (fun _ => True) ∧
    remainingRecipient.Intellectual false)

end TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork
