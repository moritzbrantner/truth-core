module

/-!
Analyst reconstruction for #1397; historical attribution deferred. One context
contains earlier/later occurrences, assigned bearers in B. B is not a body or
stage type: interpreting it as persons is OPEN. Continuation is a supplied
relation on occurrences, never defined as bearer equality or memory.
Finite controls are structural surrogates, not possible human fissions.
-/

@[expose] public section
namespace TruthCore.Mereology.Fission1397

inductive Occurrence where
  | earlier | left | right
  deriving DecidableEq

/-- Two directed continuation edges, independently of any bearer assignment. -/
def branching (s t : Occurrence) : Prop :=
  s = .earlier ∧ (t = .left ∨ t = .right)

/-- The selected continuation relation suffices for ordinary bearer identity.
No claim of its necessity, psychological adequacy or actuality is made. -/
def Sufficient {B : Type} (c : Occurrence → Occurrence → Prop)
    (b : Occurrence → B) : Prop := ∀ s t, c s t → b s = b t

def Distinct {B : Type} (b : Occurrence → B) : Prop := b .left ≠ b .right

theorem incompatible {B : Type} (c : Occurrence → Occurrence → Prop)
    (b : Occurrence → B) (hl : c .earlier .left) (hr : c .earlier .right)
    (hs : Sufficient c b) : ¬ Distinct b := by
  intro hd
  exact hd ((hs _ _ hl).symm.trans (hs _ _ hr))

/-- General symmetry obstruction. Data transformation and output transformation
need not be bijections for the proof. An automorphism of complete data is a
stronger application hypothesis; preserving only one observed relation does
not establish that completeness. The output is one bearer, not a probability,
set of successors or optional refusal. -/
def Equivariant {D B : Type} (transform : D → D) (swap : B → B)
    (choose : D → B) : Prop := ∀ d, choose (transform d) = swap (choose d)

theorem no_choice {D B : Type} (transform : D → D) (swap : B → B)
    (choose : D → B) (d : D) (a b : B)
    (fixed : transform d = d) (equiv : Equivariant transform swap choose)
    (admissible : choose d = a ∨ choose d = b)
    (sa : swap a = b) (sb : swap b = a) (distinct : a ≠ b) : False := by
  have h : choose d = swap (choose d) := (congrArg choose fixed).symm.trans (equiv d)
  rcases admissible with ha | hb
  · rw [ha, sa] at h
    exact distinct h
  · rw [hb, sb] at h
    exact distinct h.symm

/-- Earlier/later identity stays internal to each history. No equality between
individuals in different histories is used. Left and right are role indices. -/
inductive Context where
  | soloLeft | soloRight | split
  deriving DecidableEq

/-- A cross-context bridge on IDENTITY VERDICTS: deleting the other branch
preserves whether the selected role has the earlier bearer. This is substantive
and distinct from similarity of bodies, memories or local causal histories. -/
def VerdictInvariant {B : Context → Type}
    (bearer : (w : Context) → Occurrence → B w) : Prop :=
  (bearer .soloLeft .earlier = bearer .soloLeft .left ↔
    bearer .split .earlier = bearer .split .left) ∧
  (bearer .soloRight .earlier = bearer .soloRight .right ↔
    bearer .split .earlier = bearer .split .right)

theorem solo_split_conflict {B : Context → Type}
    (bearer : (w : Context) → Occurrence → B w)
    (leftSolo : bearer .soloLeft .earlier = bearer .soloLeft .left)
    (rightSolo : bearer .soloRight .earlier = bearer .soloRight .right)
    (invariant : VerdictInvariant bearer) : ¬ Distinct (bearer .split) := by
  intro hd
  exact hd ((invariant.1.mp leftSolo).symm.trans (invariant.2.mp rightSolo))

/-- Three positive rival assignments retain the same branching edges. -/
def neither : Occurrence → Occurrence := fun s => s
def leftOnly : Occurrence → Bool
  | .earlier => false | .left => false | .right => true
def collapsed : Occurrence → Unit := fun _ => ()
def noEdges (_ _ : Occurrence) : Prop := False
def onlyLeft (s t : Occurrence) : Prop := s = .earlier ∧ t = .left
def onlyRight (s t : Occurrence) : Prop := s = .earlier ∧ t = .right
def rightOnly : Occurrence → Bool
  | .earlier => true | .left => false | .right => true

def swap : Occurrence → Occurrence
  | .earlier => .earlier | .left => .right | .right => .left
def chooseLeft (_ : Unit) : Occurrence := .left
def chooseEarlier (_ : Unit) : Occurrence := .earlier
def flip : Bool → Bool | false => true | true => false
def chooseBit (d : Bool) : Occurrence := if d then .right else .left

/-- A nonbranching qualification with an explicit uniqueness requirement. -/
def UniqueContinuation (c : Occurrence → Occurrence → Prop) (s t : Occurrence) : Prop :=
  c s t ∧ ∀ u, c s u → u = t
def NonbranchSufficient {B : Type} (c : Occurrence → Occurrence → Prop)
    (b : Occurrence → B) : Prop := ∀ s t, UniqueContinuation c s t → b s = b t

/-- A solo history lacks one successor occurrence; the role name still exists
in the indexing type, but is not an admitted occurrence in that history. -/
def present : Context → Occurrence → Prop
  | .soloLeft, s => s ≠ .right
  | .soloRight, s => s ≠ .left
  | .split, _ => True
def contextualEdges (w : Context) (s t : Occurrence) : Prop :=
  branching s t ∧ present w s ∧ present w t
def contextualBearer : Context → Occurrence → Occurrence
  | .soloLeft, .earlier => .left
  | .soloRight, .earlier => .right
  | _, s => s

/-- Two trajectory labels share their earlier occurrence; their later
occurrences and whole functions differ. This is a finite structural surrogate
for overlapping continuants, not a claim that there are two actual persons. -/
def trajectory (p : Bool) (later : Bool) : Occurrence :=
  if later then (if p then .right else .left) else .earlier

def RivalControls : Prop :=
  (∀ w, NonbranchSufficient (contextualEdges w) (contextualBearer w)) ∧
  (∀ w, Distinct (contextualBearer w)) ∧
  contextualBearer .soloLeft .earlier = contextualBearer .soloLeft .left ∧
  contextualBearer .soloRight .earlier = contextualBearer .soloRight .right ∧
  ¬ VerdictInvariant contextualBearer ∧
  (trajectory false false = trajectory true false ∧
    trajectory false true ≠ trajectory true true ∧ trajectory false ≠ trajectory true)

/-- A genuine automorphism of the toy directed continuation structure, fixing
the earlier role. Completeness for a person-identity selector is NOT asserted. -/
def ToySymmetry : Prop :=
  (∀ s, swap (swap s) = s) ∧ swap .earlier = .earlier ∧
  swap .left = .right ∧ swap .right = .left ∧
  (∀ s t, branching (swap s) (swap t) ↔ branching s t)

/-- Closed certificate: generic conflicts; nonempty finite interpretations of
all three pairwise omissions in the identity triple; and separate selector
controls omitting equivariance, admissibility, data symmetry, swapping, or
distinctness. The solo theorem does not presume cross-world bearer identity.
No historical, metaphysical, Creed or root entailment is asserted. -/
def Certificate : Prop :=
  (∀ (B : Type) (c : Occurrence → Occurrence → Prop) (b : Occurrence → B),
    c .earlier .left → c .earlier .right → Sufficient c b → ¬ Distinct b) ∧
  (∀ (D B : Type) (t : D → D) (s : B → B) (f : D → B) (d : D) (a b : B),
    t d = d → Equivariant t s f → (f d = a ∨ f d = b) →
    s a = b → s b = a → a ≠ b → False) ∧
  (∀ (B : Context → Type) (b : (w : Context) → Occurrence → B w),
    b .soloLeft .earlier = b .soloLeft .left →
    b .soloRight .earlier = b .soloRight .right →
    VerdictInvariant b → ¬ Distinct (b .split)) ∧
  (branching .earlier .left ∧ branching .earlier .right ∧
    Distinct neither ∧ ¬ Sufficient branching neither) ∧
  (Sufficient noEdges neither ∧ Distinct neither) ∧
  (Sufficient branching collapsed ∧ ¬ Distinct collapsed) ∧
  (Distinct leftOnly ∧ leftOnly .earlier = leftOnly .left ∧
    leftOnly .earlier ≠ leftOnly .right) ∧
  (chooseLeft () = .left ∧ ¬ Equivariant id swap chooseLeft) ∧
  (Equivariant id swap chooseEarlier ∧
    ¬ (chooseEarlier () = .left ∨ chooseEarlier () = .right)) ∧
  (Equivariant flip swap chooseBit ∧ chooseBit false = .left ∧ flip false ≠ false) ∧
  (Equivariant id id chooseLeft ∧ chooseLeft () = .left ∧
    (id (Occurrence.left)) ≠ Occurrence.right) ∧
  (Equivariant id swap chooseEarlier ∧
    chooseEarlier () = .earlier ∧ swap .earlier = .earlier) ∧
  (Sufficient onlyLeft leftOnly ∧ Distinct leftOnly) ∧
  (Sufficient onlyRight rightOnly ∧ Distinct rightOnly) ∧ RivalControls ∧ ToySymmetry

end TruthCore.Mereology.Fission1397
