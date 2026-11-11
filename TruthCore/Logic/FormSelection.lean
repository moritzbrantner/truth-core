module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.Article1

@[expose] public section
namespace TruthCore.Logic.FormSelection
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception

/-- Structural presentation data, not a definition of cognition. `state` is
intrinsic; `decode` may depend on an external context. `target` names the
selected effect/form, without asserting its actual existence or aboutness. -/
structure Presentation (Context State Form : Type) where
  state : Context → State
  decode : Context → State → Form
  target : Context → Form

/-- Accuracy is equality relative to the supplied codebook, not reference. -/
def Accurate {C S F : Type} (p : Presentation C S F) : Prop :=
  ∀ c, p.decode c (p.state c) = p.target c

/-- An intrinsic codebook ignores context on every state. -/
def IntrinsicDecoder {C S F : Type} (p : Presentation C S F) : Prop :=
  ∀ c d s, p.decode c s = p.decode d s

/-- Both forms are positively available, including without matter; none of
these fields asserts an occurrence or intellectual grade. -/
def recipient : Model Unit Bool where
  ForeignForm := fun _ _ => True
  CanHaveForm := fun _ _ mode => mode = .withoutMatter
  Cognitive := fun _ => False
  Sensory := fun _ => False
  Intellectual := fun _ => False

/-- Same state with external decoding; target and output vary together. -/
def contextual : Presentation Bool Unit Bool where
  state := fun _ => ()
  decode := fun c _ => c
  target := fun c => c

/-- Interventions vary an object coordinate while keeping the recorded value
fixed. These are equations for two devices, not a general causal semantics. -/
def sensor (object _recorded : Bool) : Bool := object
def replay (_object recorded : Bool) : Bool := recorded

/-- A causal-source proposal fixes the referent by an independently supplied
source map. An exemplar proposal fixes it by a production plan. A constitutive
proposal fixes it by an external anchoring map. These maps are OPEN inputs,
not established causal, normative or cognitive relations. Error is separate. -/
structure ReferenceGround (Token Object Content : Type) where
  referent : Token → Object
  content : Token → Content
  condition : Object → Content

def Correct {T O F : Type} (g : ReferenceGround T O F) (t : T) : Prop :=
  g.content t = g.condition (g.referent t)

/-- A faulty code retains its independently fixed referent. -/
def faulty : ReferenceGround Unit Bool Bool where
  referent := fun _ => true
  content := fun _ => false
  condition := fun x => x

/-- Causal provenance, plan and anchor can disagree without any change to
actual content accuracy. The choice between them requires a defended ground. -/
def ground (object : Bool) : ReferenceGround Unit Bool Bool where
  referent := fun _ => object
  content := fun _ => true
  condition := fun _ => true

def Selection : Prop :=
  ∀ {C S F : Type} (p : Presentation C S F), Accurate p → IntrinsicDecoder p → ∀ c d, p.state c = p.state d → p.target c = p.target d

def Controls : Prop :=
  ForeignFormCapacity recipient () ∧
    (∀ f, recipient.ForeignForm () f ∧ recipient.CanHaveForm () f .withoutMatter) ∧
    ¬ recipient.Intellectual () ∧
    Accurate contextual ∧ contextual.state false = contextual.state true ∧
    contextual.target false ≠ contextual.target true ∧
    (∀ b, sensor b b = replay b b) ∧
    sensor true false ≠ replay true false

def ReferenceControls : Prop :=
  faulty.referent () = true ∧ ¬ Correct faulty () ∧
    Correct (ground true) () ∧ Correct (ground false) () ∧
    (ground true).referent () ≠ (ground false).referent ()

end TruthCore.Logic.FormSelection
