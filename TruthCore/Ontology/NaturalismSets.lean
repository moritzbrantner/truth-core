module

public import TruthCore.Ontology.Naturalism
public import Mathlib.SetTheory.ZFC.Basic

/-! #1109 analyst set-location profile. The small candidate domain B ⊕ S
separates physical-bearer candidates from pure-set representatives. A supplied
map S → Mathlib.ZFSet interprets representatives by actual pure sets. This is
not a small universe of all sets, a new set theory, or a claim that Lean's
mathematical inhabitants exist as object-level entities. No injectivity or
full membership-closure premise is silently imposed. -/

@[expose] public section
namespace TruthCore.Ontology.NaturalismSets
open TruthCore.Ontology.Naturalism TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

variable {W B S : Type}

/-- Weak support: each located set representative has some located
representative interpreting an actual strict member. Regions need not be the
same. This does not require every member to be represented. Existence of either
candidate is separate; no presence guard is needed for the unlocation theorem.
An empty-set representative cannot satisfy the antecedent under this rule. -/
def SetLocationHasMemberSupport (decode : S → ZFSet.{0}) (F : Frame (B ⊕ S)) : Prop :=
  ∀ s, Located F (.inr s) →
    ∃ t, decode t ∈ decode s ∧ Located F (.inr t)

/-- Positive propagation alone: a located represented member confers its
region on the represented containing set. This supplies no converse support
and imposes no restriction at all at an empty-set representative. -/
def MemberConfersSetLocation (decode : S → ZFSet.{0}) (F : Frame (B ⊕ S)) : Prop :=
  ∀ s t r, decode t ∈ decode s → F.locatedAt (.inr t) r → F.locatedAt (.inr s) r

def SetRepresentativesUnlocated (F : Frame (B ⊕ S)) : Prop :=
  ∀ s, ¬ Located F (.inr s)

def NoExistingSetRepresentatives (o : Ontic W (B ⊕ S)) (w : W) : Prop :=
  ∀ s, ¬ o.ExistsAt w (.inr s)

/-- Actual Mathlib pure sets used as a finite representative fragment. The
singleton here is {∅}, not the earlier corpus's designated {2} anchor. -/
def sampleDecode : Bool → ZFSet.{0}
  | false => ∅
  | true => {∅}

/-- Separate populated controls. Both keep actual empty/singleton membership
in the mathematical interpretation. The first has an existing located bearer
and no object-level set entities. The second has both set entities existing
and located, with positive propagation but explicitly false reverse support.
Neither purports to implement Field's complete nominalization or actual physics. -/
def Controls : Prop :=
  sampleDecode false ∈ sampleDecode true ∧
  (∀ t, sampleDecode t ∉ sampleDecode false) ∧
  (∃ (o : Ontic Unit (Unit ⊕ Bool)) (F : Frame (Unit ⊕ Bool)),
    ExistenceNaturalism o (Located F) () ∧ SetLocationHasMemberSupport sampleDecode F ∧
    o.ExistsAt () (.inl ()) ∧ Located F (.inl ()) ∧
    NoExistingSetRepresentatives o () ∧ SetRepresentativesUnlocated F) ∧
  (∃ (o : Ontic Unit (Unit ⊕ Bool)) (F : Frame (Unit ⊕ Bool)),
    ExistenceNaturalism o (Located F) () ∧ MemberConfersSetLocation sampleDecode F ∧
    ¬ SetLocationHasMemberSupport sampleDecode F ∧
    o.ExistsAt () (.inl ()) ∧ Located F (.inl ()) ∧
    o.ExistsAt () (.inr false) ∧ Located F (.inr false) ∧
    o.ExistsAt () (.inr true) ∧ Located F (.inr true))

end TruthCore.Ontology.NaturalismSets
