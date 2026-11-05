module

public import TruthCore.Explanation.DisjunctionGround

/-!
# Truthmaker scope and uniform identity (#941)

Analyst framework over the existing PSR arena. `Making` has a bearer argument,
whereas `Arena.explains` relates facts; neither is defined as efficient causation.
Soundness separately requires actual truth and existence of the maker at the
world of making. Necessitation is an additional, rigid-fact framework assumption,
not attributed to Merricks: his author précis p.1 guards it by existence of both
maker and proposition. Coverage always ranges over the supplied fact carrier;
the finite controls therefore model fragments, not all unrestricted truths.
-/

@[expose] public section
namespace TruthCore.Explanation.TruthmakerTheories
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.DisjunctionGround
open TruthCore.German.Kant.CosmologicalInference
variable {W B F : Type}

/-- A primitive, substantive making-true commitment, not material implication.
No transitivity/asymmetry/well-foundedness is assumed; those would need a typed
composition operation since makers and truthbearers have different sorts. -/
abbrev Making (W B F : Type) := W → B → F → Prop

def TruthSound (A : Arena W B F) (M : Making W B F) : Prop :=
  ∀ w b f, M w b f → A.holds w f

def WorldImmanent (A : Arena W B F) (M : Making W B F) : Prop :=
  ∀ w b f, M w b f → A.ontic.ExistsAt w b

def Sound (A : Arena W B F) (M : Making W B F) : Prop :=
  TruthSound A M ∧ WorldImmanent A M

/-- Cross-world necessitation of the truth by this bearer, without asserting the
bearer exists at all those worlds. Rigid truthbearer availability is stipulated. -/
def MakerNecessitation (A : Arena W B F) (M : Making W B F) : Prop :=
  ∀ w b f, M w b f → ∀ v, Access A w v → A.ontic.ExistsAt v b → A.holds v f

def Covers (A : Arena W B F) (M : Making W B F) (scope : F → Prop) : Prop :=
  ∀ w f, scope f → A.holds w f → ∃ b, M w b f

/-- Maximalist coverage relative to ALL represented facts, plus explicit soundness. -/
def Maximalist (A : Arena W B F) (M : Making W B F) : Prop :=
  Sound A M ∧ Covers A M (fun _ => True)

/-- No demand outside the supplied substantive scope; it does not deny makers
outside that scope. This bundle includes no exclusion axiom. -/
def Restricted (A : Arena W B F) (M : Making W B F) (scope : F → Prop) : Prop :=
  Sound A M ∧ Covers A M scope

/-- Truthmaker-free semantics imposes no coverage demand. It is NOT the claim
that no truth has a maker; both empty and nonempty sound relations are allowed. -/
def TruthmakerFree (A : Arena W B F) (M : Making W B F) : Prop := Sound A M

def ExistenceScope (A : Arena W B F) (f : F) : Prop := ∃ b, f = A.exist b

def LocalMaker (A : Arena W B F) (M : Making W B F) (a : W) (f : F) : Prop :=
  ∀ v, Access A a v → ∃ b, M v b f

def UniformMaker (A : Arena W B F) (M : Making W B F) (a : W) (f : F) : Prop :=
  ∃ b, ∀ v, Access A a v → M v b f

/-- Existing #938 fact-reasons project to bearer makers only through existence
facts. Soundness of this projection requires factivity and coherence. -/
def InstanceMaker (A : Arena W B F) : Making W B F :=
  fun w b f => A.explains w (A.exist b) f

def localMaking : Making Bool Bool DFact := fun w b f =>
  b = w ∧ (f = .some ∨ f = .exist b)

def restrictedMaking : Making Bool Bool DFact := fun w b f =>
  b = w ∧ f = .exist b

def fixedMaking : Making Bool Bool DFact := fun w b f =>
  fixedExists w b ∧ (f = .some ∨ f = .exist b)

def switchingFixedMaking : Making Bool Bool DFact := fun w b f =>
  fixedExists w b ∧ ((f = .some ∧ b = w) ∨ f = .exist b)

/-- No-maker relation, one permitted interpretation of free semantics only. -/
def noMaking : Making W B F := fun _ _ _ => False

/-! The negative truth is an additional represented fact, so its omission cannot
be hidden by using a positive-only finite fact carrier. Empty means absence of
ALL eligible makers in B, including any abstract makers if admitted to B. -/
inductive NFact | positive | empty

def negativeArena : Arena Bool Unit NFact where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w _ => w = false,
             Causes := fun _ _ _ => False }
  holds := fun w f => match f with | .positive => w = false | .empty => w = true
  exist := fun _ => .positive
  explains := fun _ _ _ => False
  conjunct := fun g f => g = f

def negativeMaking : Making Bool Unit NFact :=
  fun w _ f => w = false ∧ f = .positive

/-- Omission of world immanence: an absent candidate makes the negative truth.
A formal omission control, not an assertion that nonexistent entities can ground. -/
def outsideMaking : Making Bool Unit NFact :=
  fun w _ f => w = true ∧ f = .empty

def EmptyFact (A : Arena W B F) (f : F) : Prop :=
  ∀ w, A.holds w f ↔ ∀ b, ¬ A.ontic.ExistsAt w b

def NeedsMakerAt (A : Arena W B F) (M : Making W B F) (w : W) (f : F) : Prop :=
  A.holds w f → ∃ b, M w b f

/-- Abstract-present control for concrete-only emptiness. All eligible makers
exist; none is classified concrete. No actuality of this ontology is asserted. -/
def abstractArena : Arena Unit Unit NFact where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True,
             Causes := fun _ _ _ => False }
  holds := fun _ _ => True
  exist := fun _ => .positive
  explains := fun _ _ _ => False
  conjunct := fun g f => g = f

def abstractMaking : Making Unit Unit NFact := fun _ _ _ => True

def ConcreteEmptyFact (A : Arena W B F) (concrete : W → B → Prop) (f : F) : Prop :=
  ∀ w, A.holds w f ↔ ∀ b, ¬ concrete w b

def ConcreteMaker (M : Making W B F) (concrete : W → B → Prop) : Prop :=
  ∀ w b f, M w b f → concrete w b

/-- Full conditional comparison and named controls. No philosophical premise is
asserted by a certificate of this proposition. Models are finite fragments. -/
def TheoryMap : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (M : Making W B F) (scope : F → Prop),
    Maximalist A M → Restricted A M scope ∧ TruthmakerFree A M) ∧
  (∀ (W B F : Type) (A : Arena W B F),
    Factive A → Coherent A → Sound A (InstanceMaker A)) ∧
  (∀ (W B F : Type) (A : Arena W B F) (M : Making W B F) (a : W) (f : F),
    WorldImmanent A M → Access A a a → UniformMaker A M a f →
      NecessaryBeing A.ontic a) ∧
  (∀ (W B F : Type) (A : Arena W B F) (M : Making W B F) (a : W) (f : F),
    Maximalist A M → TruthCore.Explanation.StoppingPoints.NecessaryFact A a f →
      LocalMaker A M a f) ∧
  (Maximalist truthmakers localMaking ∧ MakerNecessitation truthmakers localMaking ∧
    LocalMaker truthmakers localMaking false .some ∧
    ¬ UniformMaker truthmakers localMaking false .some ∧
    ¬ NecessaryBeing truthmakers.ontic false) ∧
  (Restricted truthmakers restrictedMaking (ExistenceScope truthmakers) ∧
    (∃ f, ExistenceScope truthmakers f ∧ truthmakers.holds false f ∧
      ∃ b, restrictedMaking false b f) ∧
    truthmakers.holds false .some ∧ ¬ ∃ b, restrictedMaking false b .some ∧
    ¬ Maximalist truthmakers restrictedMaking) ∧
  (TruthmakerFree truthmakers noMaking ∧ TruthmakerFree truthmakers localMaking ∧
    (∃ b f, localMaking false b f) ∧ ¬ LocalMaker truthmakers noMaking false .some) ∧
  (Maximalist fixedBearer fixedMaking ∧ MakerNecessitation fixedBearer fixedMaking ∧
    UniformMaker fixedBearer fixedMaking false .some ∧
    NecessaryBeing fixedBearer.ontic false ∧
    (∀ w b c, ¬ fixedBearer.ontic.Causes w b c)) ∧
  (Maximalist fixedBearer switchingFixedMaking ∧
    NecessaryBeing fixedBearer.ontic false ∧
    ¬ UniformMaker fixedBearer switchingFixedMaking false .some) ∧
  (UniformGround lawGround false .some ∧
    ∀ M : Making Bool Bool DFact, WorldImmanent lawGround M →
      ¬ UniformMaker lawGround M false .some)

def NegativeMap : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (M : Making W B F) (w : W) (f : F),
    EmptyFact A f → A.holds w f → NeedsMakerAt A M w f →
      WorldImmanent A M → False) ∧
  (EmptyFact negativeArena .empty ∧ Coherent negativeArena ∧
    Restricted negativeArena negativeMaking (ExistenceScope negativeArena) ∧
    (∃ f, ExistenceScope negativeArena f ∧ negativeArena.holds false f ∧
      ∃ b, negativeMaking false b f) ∧
    negativeArena.holds true .empty ∧
    ¬ Maximalist negativeArena negativeMaking) ∧
  -- Drop emptiness, coverage, immanence respectively, retaining truth soundness.
  (¬ negativeArena.holds false .empty ∧
    NeedsMakerAt negativeArena noMaking false .empty ∧ Sound negativeArena noMaking) ∧
  (negativeArena.holds true .empty ∧ Sound negativeArena noMaking ∧
    ¬ NeedsMakerAt negativeArena noMaking true .empty) ∧
  (negativeArena.holds true .empty ∧
    NeedsMakerAt negativeArena outsideMaking true .empty ∧
    TruthSound negativeArena outsideMaking ∧ ¬ WorldImmanent negativeArena outsideMaking) ∧
  -- Concrete-empty need not be absolutely empty: an existing abstract maker.
  (Maximalist abstractArena abstractMaking ∧
    ConcreteEmptyFact abstractArena (fun _ _ => False) .empty ∧
    (∀ b : Unit, ¬ (fun (_ : Unit) (_ : Unit) => False) () b) ∧
    (∃ b, abstractMaking () b .empty ∧ abstractArena.ontic.ExistsAt () b) ∧
    ¬ ConcreteMaker abstractMaking (fun _ _ => False))

/-- Strong restricted-scope separation, with existential parentheses explicit.
The earlier frozen map has a weaker negative conjunct; this companion supplies
the substantive noncoverage/nonmaximalism result without changing that target. -/
def RestrictedSeparation : Prop :=
  Restricted truthmakers restrictedMaking (ExistenceScope truthmakers) ∧
  truthmakers.holds false .some ∧
  (¬ ∃ b, restrictedMaking false b .some) ∧
  ¬ Maximalist truthmakers restrictedMaking

/-- Full truth-set language on the SAME two-world alternating ontology. It is
closed under ordinary negation and conjunction. This is a truth-conditional
language, not a claim that every metaphysical/aboutness thesis is represented. -/
def truthSetArena : Arena Bool Bool (Bool → Prop) where
  ontic := truthmakers.ontic
  holds := fun w p => p w
  exist := fun b w => b = w
  explains := fun _ _ _ => False
  conjunct := fun g f => ∀ w, f w → g w

def truthSetMaking : Making Bool Bool (Bool → Prop) :=
  fun w b p => b = w ∧ p w

def TruthSetMap : Prop :=
  Maximalist truthSetArena truthSetMaking ∧
  MakerNecessitation truthSetArena truthSetMaking ∧
  Coherent truthSetArena ∧
  (∀ p : Bool → Prop, ∃ q : Bool → Prop,
    ∀ w, truthSetArena.holds w q ↔ ¬ truthSetArena.holds w p) ∧
  (∀ p q : Bool → Prop, ∃ r : Bool → Prop,
    ∀ w, truthSetArena.holds w r ↔
      truthSetArena.holds w p ∧ truthSetArena.holds w q) ∧
  TruthCore.Explanation.StoppingPoints.NecessaryFact truthSetArena false (fun _ => True) ∧
  LocalMaker truthSetArena truthSetMaking false (fun _ => True) ∧
  (¬ UniformMaker truthSetArena truthSetMaking false (fun _ => True)) ∧
  ¬ NecessaryBeing truthSetArena.ontic false

end TruthCore.Explanation.TruthmakerTheories
