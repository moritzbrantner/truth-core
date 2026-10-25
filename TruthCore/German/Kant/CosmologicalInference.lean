import TruthCore.Modal.Kripke

/-!
Small tests of contested bridges in CPR A238–248/B297–305, A458–460/B486–488,
A560–567/B588–595 and A605–610/B633–638. These are reconstructions, not a
formalization of transcendental idealism. Worlds and modal accessibility reuse
`TruthCore.Modal.Frame`; causal dependence is a separate relation. A modal
countermodel does not by itself establish real possibility in Kant's sense.
-/
namespace TruthCore.German.Kant.CosmologicalInference

/-- A constant domain of candidate beings, world-relative existence, and a
causal relation. Candidates need not exist in every world. No PSR, well-founded
regress, or application beyond experience is built into the signature. -/
structure Ontic (World Entity : Type) where
  frame : TruthCore.Modal.Frame World
  ExistsAt : World → Entity → Prop
  Causes : World → Entity → Entity → Prop

/-- A de re modal surrogate for inability not to be, relative to the stated
frame. Not Scott's essence-based NE, timeless duration, or Kantian cognition. -/
def NecessaryAt (m : Ontic W E) (w : W) (x : E) : Prop :=
  ∀ v, m.frame.access w v → m.ExistsAt v x

/-- Present existence together with accessible nonexistence of that individual. -/
def ContingentAt (m : Ontic W E) (w : W) (x : E) : Prop :=
  m.ExistsAt w x ∧ ∃ v, m.frame.access w v ∧ ¬m.ExistsAt v x

/-- Every existing contingent individual has a distinct existing cause. This
local principle omits an explanation of the series as a whole and termination.
It is an analyst's surrogate of the causal premise criticized at A609/B637,
not a claim that Kant admits its unrestricted metaphysical application. -/
def LocalCausalPrinciple (m : Ontic W E) : Prop :=
  ∀ w x, ContingentAt m w x →
    ∃ y, m.ExistsAt w y ∧ m.Causes w y x ∧ y ≠ x

/-- A necessary being exists at the selected standpoint, with actual existence
explicit so that frames with no successors cannot create an existent by vacuity. -/
def NecessaryBeing (m : Ontic W E) (w : W) : Prop :=
  ∃ x, m.ExistsAt w x ∧ NecessaryAt m w x

/-- A countermodel to the local-causality-only step from a contingent being to
a necessary one (A605/B633n, A609–610/B637–638). Not a countermodel to the Ways
with their additional per se regress/act-potency premises. -/
def LocalCausalityInsufficient : Prop :=
  ∃ m : Ontic Bool (Bool × Nat),
    LocalCausalPrinciple m ∧
    (∃ x, ContingentAt m false x) ∧ ¬NecessaryBeing m false

/-- Extensional bookkeeping for positive realities. A feature's being a
positive reality is supplied by the interpretation; this signature does not
identify maximal reality with maximal being, pure act, or the Catholic God. -/
structure RealityProfile (Entity : Type) where
  Feature : Type
  Has : Entity → Feature → Prop

/-- Possessing every feature of the chosen positive-reality profile. The
choice and adequacy of that profile remain interpretive obligations. -/
def MostReal (p : RealityProfile E) (x : E) : Prop := ∀ f, p.Has x f

/-- The disputed identification premise of Kant's reported proof, A608/B636.
It is a premise of the opponent as reconstructed by Kant, not Kant's belief. -/
def NecessaryIsMostReal (m : Ontic W E) (p : RealityProfile E) (w : W) : Prop :=
  ∀ x, NecessaryAt m w x → MostReal p x

/-- Strong identity reading of A608–609/B636–637's assertion that most-real
beings do not differ. Mere indiscernibility need not mean numerical identity;
this sufficient reconstruction is marked separately in the disambiguation. -/
def MostRealUnique (p : RealityProfile E) : Prop :=
  ∀ x y, MostReal p x → MostReal p y → x = y

/-- The conversion's restricted conclusion: every most-real candidate is
necessary at the selected world. It is not an a priori proof of existence. -/
def MostRealIsNecessary (m : Ontic W E) (p : RealityProfile E) (w : W) : Prop :=
  ∀ x, MostReal p x → NecessaryAt m w x

/-- Necessary existence alone cannot identify a most-real being; the explicit
positive-reality interpretation prevents this being an opaque Prop exercise. -/
def IdentificationNeedsBridge : Prop :=
  ∃ (m : Ontic Bool Bool) (p : RealityProfile Bool),
    NecessaryBeing m false ∧ ¬∃ x, m.ExistsAt false x ∧ MostReal p x

/-- Epistemic alternatives are *interpretations*, not metaphysical successors.
Knowledge here means truth in every epistemically available interpretation. -/
def KnowsNecessary (family : S → Ontic W E) (available : S → Prop) (w : W) : Prop :=
  ∀ s, available s → NecessaryBeing (family s) w

/-- Knowing nonexistence differs from failing to know existence. -/
def KnowsNoNecessary (family : S → Ontic W E) (available : S → Prop) (w : W) : Prop :=
  ∀ s, available s → ¬NecessaryBeing (family s) w

/-- Schematic epistemic test of A562–564/B590–592: withholding both verdicts is
compatible with a necessary being in the designated actual interpretation.
This does not establish its real possibility or prove Kant's whole philosophy. -/
def WithholdingCompatibleWithBeing : Prop :=
  ∃ family : Bool → Ontic Bool Bool,
    NecessaryBeing (family true) false ∧
    ¬KnowsNecessary family (fun _ => True) false ∧
    ¬KnowsNoNecessary family (fun _ => True) false

/-- Kant A458–460/B486–488 distinguishes change over time from a contrary
state's modal availability at the same time. The model's worlds are universal
and its time coordinate is held fixed in the modal test. -/
def ChangeDoesNotGiveModalContingency : Prop :=
  ∃ (frame : TruthCore.Modal.Frame Bool) (state : Bool → Bool → Prop),
    (∀ w v, frame.access w v) ∧ state false false ∧ ¬state false true ∧
    ¬∃ w, frame.access false w ∧ ¬state w false

end TruthCore.German.Kant.CosmologicalInference
