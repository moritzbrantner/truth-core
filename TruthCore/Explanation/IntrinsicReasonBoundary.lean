module

public import TruthCore.Explanation.ExistencePSR
public import TruthCore.Causality.JointGroups
public import TruthCore.Causality.NecessarilyUnderived

/-!
# Nature-indexed existential reasons: a limited classification theorem

Analyst reconstruction for #1595/#319, not a source-attributed argument.
Leibniz, Monadology §§44–45 proposes an intrinsic existence reason for the
necessary final ground. Spinoza, Ethics I def.1 and I7–8 note II distinguishes
a reason in the individual's nature from a reason apart from it. The consulted
passages (Monadology §§44–45; Ethics I def. 1, I7, I8 note II, I11) do not
describe a temporally prior self-producer; the relation of *causa sui* to
efficient causation (Ethics I16 cor. 1, I25 schol.) is not examined here.

Compiled in the library build but unregistered: no Challenge, argument,
result or Comparator configuration, so nothing here is certified.

The theorem classifies constituents of ONE true, worldwise sufficient candidate
record for an actual existence fact. It exposes separately the disputed move
from foreign-nature/external reason to actual esse-support and the exclusion
of global-structural and fact-copy constituents. `Groups.admitted`, truth,
worldwise sufficiency and nature tags do NOT establish explanatory direction,
complete metaphysical adequacy or an independently real nature. Consequently
this is not yet a formalization of STMT-NECESSARY-GROUND-HAS-INTRINSIC-REASON.
See docs/notes/intrinsic-existence-reason-1595.md.
-/

@[expose] public section

namespace TruthCore.Explanation.IntrinsicReasonBoundary

open TruthCore.Explanation.ExistencePSR
open TruthCore.Causality.JointGroups
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

/-- A purported real-nature ingredient names its bearer; its label is not an
independent demonstration that such a nature obtains or explains existence.
An external ingredient can be about another actual bearer; a global ingredient
need not be borne by an individual.

`nature b f` and `external b f` carry the same data (`Being × Feature`): for
one bearer the nature/external split is a constructor TAG, not a typed content
difference. Exhaustiveness of the three-way classification is fixed by this
closed inductive type (`global` over an arbitrary `Structure` is the catch-all
for reasons not borne by one individual); it is therefore not a premise of
`selectedNatureRecord`, while its adequacy as a classification of real reasons
stays an open interpretive question. -/
inductive Ingredient (Being Feature Structure : Type) where
  | nature : Being → Feature → Ingredient Being Feature Structure
  | external : Being → Feature → Ingredient Being Feature Structure
  | global : Structure → Ingredient Being Feature Structure

/-- An existence-fact label is kept separate from proposed reason ingredients.
It is intentionally possible to put a fact label into a candidate antecedent;
the theorem must exclude that copying, rather than hide it in the type. -/
abbrev Item (B F S : Type) := Sum (ExistenceFact B) (Ingredient B F S)

def positive {B F S : Type} (n : B) : Item B F S := .inl (.fact n)

/-- Modal sufficiency of the whole antecedent record within the selected
accessibility relation. This is truth consequence, not metaphysical grounding. -/
def WorldwiseSufficient (m : Ontic W B) (h : Groups (Item B F S) G)
    (holds : W → Item B F S → Prop) (w : W) (n : B) (g : G) : Prop :=
  ∀ v, m.frame.access w v →
    (∀ i, i ∈ h.members g → holds v i) → m.ExistsAt v n

/-- One witnessed nonempty candidate reason of THIS actual individual's
existence fact, with all full-record contributors and enablers retained.
Neither admission nor sufficiency gives explanatory priority or relevance. -/
def ActualRecord (m : Ontic W B) (h : Groups (Item B F S) G)
    (holds : W → Item B F S → Prop) (w : W) (n : B) (g : G) : Prop :=
  h.admitted g ∧ h.effect g = positive n ∧
  (∃ i, i ∈ h.members g) ∧
  (∀ i, i ∈ h.members g → holds w i) ∧
  m.ExistsAt w n ∧ WorldwiseSufficient m h holds w n g

/-- The exact candidate conclusion retains the SAME full record and every
one of its ingredients, instead of selecting an ingredient and pretending it
alone constitutes a complete explanation. -/
def IntrinsicOnlyRecord (m : Ontic W B) (h : Groups (Item B F S) G)
    (holds : W → Item B F S → Prop) (w : W) (n : B) : Prop :=
  ∃ g, ActualRecord m h holds w n g ∧
    (∃ feature, (Sum.inr (.nature n feature) : Item B F S) ∈ h.members g) ∧
    ∀ i, i ∈ h.members g →
      ∃ feature, i = (Sum.inr (.nature n feature) : Item B F S)

/-- Under the chosen existential-support interpretation, foreign or external
ingredients of an ACTUAL sufficient record are asserted to furnish an actual
existential supporter. This is a separately open bridge: a noncausal abstract
reason or global law need not satisfy it. -/
def ForeignReasonSupports (m : Ontic W B)
    (support : W → B → B → Prop) (h : Groups (Item B F S) G)
    (holds : W → Item B F S → Prop) (w : W) (n : B) : Prop :=
  (∀ g b feature, ActualRecord m h holds w n g →
    (Sum.inr (.external b feature) : Item B F S) ∈ h.members g →
    m.ExistsAt w b ∧ support w b n) ∧
  (∀ g b feature, ActualRecord m h holds w n g → b ≠ n →
    (Sum.inr (.nature b feature) : Item B F S) ∈ h.members g →
    m.ExistsAt w b ∧ support w b n)

/-- Neither an actual source relation nor modal necessity rules out an
explanatory fact-copy or a genuinely global reason. These are additional
and separately testable scope premises. -/
def NoFactOrGlobalMember (m : Ontic W B) (h : Groups (Item B F S) G)
    (holds : W → Item B F S → Prop) (w : W) (n : B) : Prop :=
  (∀ g b, ActualRecord m h holds w n g →
    (Sum.inl (.fact b) : Item B F S) ∉ h.members g) ∧
  (∀ g s, ActualRecord m h holds w n g →
    (Sum.inr (.global s) : Item B F S) ∉ h.members g)

/-- A typed conditional positive result, not an opaque `A → conclusion`
bridge. The source is underived *in the support relation*, and only the
explicit reason/support bridge eliminates foreign and external constituents.
No fact-copy/global constituent is silently treated as an individual cause.
The recorded nonempty group cannot disappear after classification.

This proves nothing about genuine explanatory relevance or whether the named
nature-feature is a real/adequate reason for existence. -/
theorem selectedNatureRecord
    (m : Ontic W B) (support : W → B → B → Prop)
    (h : Groups (Item B F S) G) (holds : W → Item B F S → Prop)
    (w : W) (n : B)
    (hRecord : ∃ g, ActualRecord m h holds w n g)
    (hSource : NoExistingSupportAt m support w n)
    (hBridge : ForeignReasonSupports m support h holds w n)
    (hScope : NoFactOrGlobalMember m h holds w n) :
    IntrinsicOnlyRecord m h holds w n := by
  rcases hRecord with ⟨g, hg⟩
  rcases hBridge with ⟨hExternal, hOtherNature⟩
  rcases hScope with ⟨hNoFact, hNoGlobal⟩
  have allOwn : ∀ i, i ∈ h.members g →
      ∃ feature, i = (Sum.inr (.nature n feature) : Item B F S) := by
    intro i hi
    cases i with
    | inl fact =>
      cases fact with
      | fact b => exact False.elim ((hNoFact g b hg) hi)
    | inr ingredient =>
      cases ingredient with
      | nature b feature =>
        by_cases hSame : b = n
        · subst b
          exact ⟨feature, rfl⟩
        · have hs := hOtherNature g b feature hg hSame hi
          exact False.elim (hSource b hs.1 hs.2)
      | external b feature =>
        have hs := hExternal g b feature hg hi
        exact False.elim (hSource b hs.1 hs.2)
      | global s =>
        exact False.elim ((hNoGlobal g s hg) hi)
  rcases hg.2.2.1 with ⟨i, hi⟩
  rcases allOwn i hi with ⟨feature, hEq⟩
  refine ⟨g, hg, ⟨feature, ?_⟩, allOwn⟩
  exact hEq ▸ hi

/-! ### Populated finite omission controls

The first controls use the same nonempty always-existing bearer, universal
two-world accessibility, and empty actual esse-support relation. They change
the *one* nonempty reason ingredient, not an existence or modal truth
assignment. Each omission control proves, in one model, every other
hypothesis of `selectedNatureRecord`, the failure of the omitted one, and the
failure of the conclusion. Their members are only candidate reasons, so they
demonstrate the necessity of interpretation bridges, not adequate rival
metaphysical explanations.
-/

def populated : Ontic Bool Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

def noSupport : Bool → Unit → Unit → Prop := fun _ _ _ => False

def single (item : Item Unit Unit Unit) : Groups (Item Unit Unit Unit) Unit where
  contributors := fun _ => {item}
  enablers := fun _ => ∅
  effect := fun _ => positive ()
  admitted := fun _ => True

def allHold : Bool → Item Unit Unit Unit → Prop := fun _ _ => True

theorem singleActual (item : Item Unit Unit Unit) :
    ActualRecord populated (single item) allHold false () () := by
  refine ⟨trivial, rfl, ⟨item, ?_⟩, ?_, trivial, ?_⟩
  · simp [single, Groups.members]
  · intro i hi
    trivial
  · intro v hv hall
    trivial

theorem populatedUnderivedNecessary :
    NecessaryAt populated false () ∧
    NoExistingSupportAt populated noSupport false () := by
  constructor
  · intro v hv
    trivial
  · intro source hExists hSupport
    exact hSupport

/-- Positive *syntactic* nature record, without the extra metaphysical
adequacy claim. The actualness/sufficiency side conditions are populated. -/
theorem natureCandidate :
    ActualRecord populated (single (.inr (.nature () ()))) allHold false () () ∧
    IntrinsicOnlyRecord populated (single (.inr (.nature () ()))) allHold false () := by
  constructor
  · exact singleActual _
  · refine ⟨(), singleActual _, ⟨(), ?_⟩, ?_⟩
    · simp [single, Groups.members]
    · intro i hi
      have h : i = (Sum.inr (.nature () ()) : Item Unit Unit Unit) := by
        simpa [single, Groups.members] using hi
      subst i
      exact ⟨(), rfl⟩

/-- Unlike a proof from contradictory bridge premises, the entire selected
conditional input package has one inhabited, actual, nonempty interpretation.
This establishes consistency only in the tiny *candidate-record* semantics. -/
theorem natureInputNonvacuous :
    (∃ g, ActualRecord populated
      (single (.inr (.nature () ()))) allHold false () g) ∧
    NoExistingSupportAt populated noSupport false () ∧
    ForeignReasonSupports populated noSupport
      (single (.inr (.nature () ()))) allHold false () ∧
    NoFactOrGlobalMember populated
      (single (.inr (.nature () ()))) allHold false () ∧
    IntrinsicOnlyRecord populated
      (single (.inr (.nature () ()))) allHold false () := by
  refine ⟨⟨(), singleActual _⟩, populatedUnderivedNecessary.2, ?_, ?_,
    natureCandidate.2⟩
  · constructor
    · intro g b feature hRec hMember
      simp [single, Groups.members] at hMember
    · intro g b feature hRec hDifferent hMember
      cases b
      exact False.elim (hDifferent rfl)
  · constructor
    · intro g b hRec hMember
      simp [single, Groups.members] at hMember
    · intro g s hRec hMember
      simp [single, Groups.members] at hMember

/-- Omit the foreign-reason-to-support bridge, with an external-TAGGED,
SELF-BORNE ingredient (`external () ()` has the target as bearer, since
`Being = Unit`). Every other hypothesis holds and the bridge fails. This shows
only that the tag alone defeats the conclusion; see
`foreignExternalWithoutSupportBridge` for an ingredient about another bearer. -/
theorem externalWithoutSupportBridge :
    ActualRecord populated (single (.inr (.external () ()))) allHold false () () ∧
    NecessaryAt populated false () ∧
    NoExistingSupportAt populated noSupport false () ∧
    NoFactOrGlobalMember populated
      (single (.inr (.external () ()))) allHold false () ∧
    ¬ ForeignReasonSupports populated noSupport
      (single (.inr (.external () ()))) allHold false () ∧
    ¬ IntrinsicOnlyRecord populated
      (single (.inr (.external () ()))) allHold false () := by
  refine ⟨singleActual _, populatedUnderivedNecessary.1,
    populatedUnderivedNecessary.2, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro g b hRec hMember
    simp [single, Groups.members] at hMember
  · intro g s hRec hMember
    simp [single, Groups.members] at hMember
  · intro hBridge
    exact (hBridge.1 () () () (singleActual _)
      (by simp [single, Groups.members])).2
  · intro h
    rcases h with ⟨g, hRec, ⟨feature, hMember⟩, _⟩
    cases g
    simp [single, Groups.members] at hMember

/-- Omit the global-reason exclusion: the same actual, necessary, underived
bearer has a candidate sufficient record whose sole member is `global`.
Every other hypothesis (including the vacuously true foreign-reason bridge)
holds and global-exclusion fails. -/
theorem globalWithoutScopeBridge :
    ActualRecord populated (single (.inr (.global ()))) allHold false () () ∧
    NecessaryAt populated false () ∧
    NoExistingSupportAt populated noSupport false () ∧
    ForeignReasonSupports populated noSupport
      (single (.inr (.global ()))) allHold false () ∧
    ¬ NoFactOrGlobalMember populated
      (single (.inr (.global ()))) allHold false () ∧
    ¬ IntrinsicOnlyRecord populated
      (single (.inr (.global ()))) allHold false () := by
  refine ⟨singleActual _, populatedUnderivedNecessary.1,
    populatedUnderivedNecessary.2, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro g b feature hRec hMember
    simp [single, Groups.members] at hMember
  · intro g b feature hRec hDifferent hMember
    simp [single, Groups.members] at hMember
  · intro hScope
    exact hScope.2 () () (singleActual _) (by simp [single, Groups.members])
  · intro h
    rcases h with ⟨g, hRec, ⟨feature, hMember⟩, _⟩
    cases g
    simp [single, Groups.members] at hMember

/-! ### A foreign-bearer external control

Two always-existing beings (`true` is the target, `false` another bearer),
universal two-world accessibility, empty esse-support. The sole member is an
external ingredient about the OTHER bearer. -/

def twoBeings : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

def noSupportTwo : Bool → Bool → Bool → Prop := fun _ _ _ => False

def foreignExternal : Groups (Item Bool Unit Unit) Unit where
  contributors := fun _ => {(Sum.inr (.external false ()) : Item Bool Unit Unit)}
  enablers := fun _ => ∅
  effect := fun _ => positive true
  admitted := fun _ => True

def allHoldTwo : Bool → Item Bool Unit Unit → Prop := fun _ _ => True

theorem foreignExternalActual :
    ActualRecord twoBeings foreignExternal allHoldTwo false true () := by
  refine ⟨trivial, rfl, ⟨Sum.inr (.external false ()), ?_⟩, ?_, trivial, ?_⟩
  · simp [foreignExternal, Groups.members]
  · intro i hi
    trivial
  · intro v hv hall
    trivial

/-- Omit the foreign-reason-to-support bridge with a candidate external reason
borne by a distinct existing being. Underivedness in the (empty) support
relation and de re necessity hold, every other hypothesis holds, and both the
bridge and the conclusion fail. Within these stipulated candidate semantics,
underivedness in the support relation does not exclude an external candidate
reason; the record need not be an adequate explanation. -/
theorem foreignExternalWithoutSupportBridge :
    ActualRecord twoBeings foreignExternal allHoldTwo false true () ∧
    NecessaryAt twoBeings false true ∧
    NoExistingSupportAt twoBeings noSupportTwo false true ∧
    NoFactOrGlobalMember twoBeings foreignExternal allHoldTwo false true ∧
    ¬ ForeignReasonSupports twoBeings noSupportTwo
      foreignExternal allHoldTwo false true ∧
    ¬ IntrinsicOnlyRecord twoBeings foreignExternal allHoldTwo false true := by
  refine ⟨foreignExternalActual, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro v hv
    trivial
  · intro source hExists hSupport
    exact hSupport
  · intro g b hRec hMember
    simp [foreignExternal, Groups.members] at hMember
  · intro g s hRec hMember
    simp [foreignExternal, Groups.members] at hMember
  · intro hBridge
    exact (hBridge.1 () false () foreignExternalActual
      (by simp [foreignExternal, Groups.members])).2
  · intro h
    rcases h with ⟨g, hRec, ⟨feature, hMember⟩, _⟩
    cases g
    simp [foreignExternal, Groups.members] at hMember

end TruthCore.Explanation.IntrinsicReasonBoundary
