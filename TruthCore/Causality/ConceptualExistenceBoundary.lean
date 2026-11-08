module

/-! Analyst reconstruction; attribution deferred. A profile is a predicate on
features, not an existing object. Candidate-domain membership entails neither
actuality nor existence. No claim about Meinong's historical theory is made. -/
@[expose] public section
namespace TruthCore.Causality.ConceptualExistenceBoundary

/-- Independent semantic inputs. `nuclear` specifies a description;
`exemplifies` is ordinary property possession, `actual` realization, and
`exists` actual existence. No field relates these primitives automatically.
A golden mountain can be characterized without possessing gold or existing. -/
structure Interpretation (Candidate Feature : Type) where
  nuclear : Feature → Prop
  exemplifies : Candidate → Feature → Prop
  actual : Candidate → Prop
  Exists : Candidate → Prop

/-- The selected candidate exemplifies the description's nuclear features.
This is an OPEN predication bridge, not a consequence of naming a candidate. -/
def Transfer (m : Interpretation C F) (c : C) : Prop :=
  ∀ f, m.nuclear f → m.exemplifies c f

/-- Some nuclear feature has an actuality-entailing extension. This explicitly
contested semantic commitment excludes purely nuclear characterization as enough.
It neither constructs a candidate nor identifies one with GOD_4. -/
def Anchor (m : Interpretation C F) : Prop :=
  ∃ f, m.nuclear f ∧ ∀ c, m.exemplifies c f → m.actual c

/-- OPEN actuality-to-actual-existence bridge; not definitional equality. -/
def ActualityExists (m : Interpretation C F) : Prop :=
  ∀ c, m.actual c → m.Exists c

/-- Existing exemplar, including every required feature of the description. -/
def ExistingExemplar (m : Interpretation C F) : Prop :=
  ∃ c, m.Exists c ∧ ∀ f, m.nuclear f → m.exemplifies c f

/-- Finite interpretations for nonvacuity and each carrying omission. All
nuclear profiles are inhabited (feature true); Unit supplies a characterized
candidate but never supplies its actual existence by construction. -/
def fixture (possesses realizes being : Prop) : Interpretation Unit Bool :=
  ⟨fun f => f = true, fun _ _ => possesses, fun _ => realizes, fun _ => being⟩

def Controls : Prop :=
  (Transfer (fixture True True True) () ∧ Anchor (fixture True True True) ∧
    ActualityExists (fixture True True True) ∧ ExistingExemplar (fixture True True True)) ∧
  (¬ Transfer (fixture False False False) () ∧ Anchor (fixture False False False) ∧
    ActualityExists (fixture False False False) ∧ ¬ ExistingExemplar (fixture False False False)) ∧
  (Transfer (fixture True False False) () ∧ ¬ Anchor (fixture True False False) ∧
    ActualityExists (fixture True False False) ∧ ¬ ExistingExemplar (fixture True False False)) ∧
  (Transfer (fixture True True False) () ∧ Anchor (fixture True True False) ∧
    ¬ ActualityExists (fixture True True False) ∧ ¬ ExistingExemplar (fixture True True False))
end TruthCore.Causality.ConceptualExistenceBoundary
