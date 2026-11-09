module

public import Mathlib.Tactic

/-! Analyst candidates for the immutable-to-eternal route. None completes the
original q.10 senses. All comparisons refer to one fixed subject/aspect/frame.
Motion segments carry a motion label, start and extent in commensurable units.
The comparison and matching below are operational stipulations, not clock physics.
Substantial configurations explicitly include possibilities beyond actual history.
-/
@[expose] public section
namespace TruthCore.Causality.DurationMeasureCandidates

structure Segment where
  motion : Bool
  start : ℕ
  extent : ℕ

def Joins (a b c : Segment) : Prop :=
  a.motion = b.motion ∧ c.motion = a.motion ∧
  b.start = a.start + a.extent ∧ c.start = a.start ∧
  c.extent = a.extent + b.extent

def NoLonger (a b : Segment) : Prop := a.extent ≤ b.extent

/-- Adequate interval comparison, including reflection; no additive unit claim. -/
def Comparative (r : Segment → ℕ) : Prop :=
  ∀ a b, NoLonger a b ↔ r a ≤ r b

/-- Cross-motion matching is independent of the proposed readout. In this
commensurable toy frame it is explicitly equality of stipulated extents. -/
def Matches (a b : Segment) : Prop := a.extent = b.extent

/-- A stronger, distinct candidate: normalized homogeneous units, concatenation,
zero, and independently fixed cross-motion matches must all be respected.
Every motion has a representative of every extent, hence matching coverage. -/
def Extensive (r : Segment → ℕ) : Prop :=
  Comparative r ∧
  (∀ a, a.extent = 0 → r a = 0) ∧
  (∀ a, a.extent = 1 → r a = 1) ∧
  (∀ a b c, Joins a b c → r c = r a + r b) ∧
  (∀ a b, Matches a b ↔ r a = r b) ∧
  (∀ a motion, ∃ b, b.motion = motion ∧ Matches a b)

def length (a : Segment) : ℕ := a.extent

def bent (a : Segment) : ℕ := a.extent * a.extent

/-- Admissibility is a supplied accessibility interpretation, not actualness.
Internal parts are tokens of substantial phases; all-at-once requires any two
admitted tokens to coincide, rather than just a constant observed state.
Inventory is a stipulated substantial holding magnitude, not elapsed clock time. -/
structure HoldingFrame (Config Part : Type) where
  admissible : Config → Prop
  actual : Config → Prop
  actual_admissible : ∀ c, actual c → admissible c
  identity : Config → ℕ
  inventory : Config → ℕ
  capacities : Config → Set ℕ
  internal : Config → Part → Prop
  adjunct : Config → ℕ

def StableWhole {C P : Type} (f : HoldingFrame C P) : Prop :=
  (∃ c, f.actual c) ∧
  (∀ c d, f.admissible c → f.admissible d → f.identity c = f.identity d) ∧
  (∀ c, f.admissible c → ∃ p, f.internal c p) ∧
  (∀ c p q, f.admissible c → f.internal c p → f.internal c q → p = q)

/-- Nonnumeric comparison candidate: representation in a partial order reflects
and preserves the independently stipulated comparison of substantial holdings.
No unit or additivity is inferred. -/
def ComparativeAevum {C P Q : Type} [PartialOrder Q]
    (f : HoldingFrame C P) (r : Set ℕ → Q) : Prop :=
  StableWhole f ∧
  (∀ a b, a ⊆ b ↔ r a ≤ r b) ∧
  (∀ c d, f.admissible c → f.admissible d → f.capacities c = f.capacities d)

/-- Quantitative candidate measures explicit holding inventories in unit counts.
This is a commensurable magnitude candidate, not a measure of elapsed time.
Its zero/unit/addition laws apply to quantities, not successive substantial parts. -/
def QuantitativeAevum {C P : Type} (f : HoldingFrame C P)
    (r : ℕ → ℕ) : Prop :=
  StableWhole f ∧ r 0 = 0 ∧ r 1 = 1 ∧
  (∀ m n, r (m+n) = r m + r n) ∧
  (∀ m n, m ≤ n ↔ r m ≤ r n) ∧
  (∀ c d, f.admissible c → f.admissible d → f.inventory c = f.inventory d)

/-- Same subject, one actual configuration, two admissible adjunct possibilities. -/
def potential : HoldingFrame Bool Unit where
  admissible := fun _ => True
  actual := fun c => c = false
  actual_admissible := by intros; trivial
  identity := fun _ => 7
  inventory := fun _ => 1
  capacities := fun _ => {0}
  internal := fun _ _ => True
  adjunct := fun c => if c then 1 else 0

def corrupted : HoldingFrame Bool Unit :=
  { potential with identity := fun c => if c then 8 else 7 }

def TimeControls : Prop :=
  Extensive length ∧ Comparative bent ∧ ¬ Extensive bent ∧
  ¬ Comparative (fun _ => 0)

def AevumControls : Prop :=
  ComparativeAevum potential (id : Set ℕ → Set ℕ) ∧
  QuantitativeAevum potential id ∧
  (∃ c d, potential.admissible c ∧ potential.admissible d ∧
    potential.adjunct c ≠ potential.adjunct d) ∧
  (∀ c d, potential.actual c → potential.actual d →
    potential.adjunct c = potential.adjunct d) ∧
  ¬ StableWhole corrupted

end TruthCore.Causality.DurationMeasureCandidates
