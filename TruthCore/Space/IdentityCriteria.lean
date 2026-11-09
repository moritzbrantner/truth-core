module

public import Mathlib.GroupTheory.GroupAction.Basic

/-!
Analyst spatial identity criteria, with attribution and world applicability open.
C is the full supplied representation carrier; B fixes a body domain, R a
relational signature, and data assigns predicates on finite body tuples. No
Euclidean, finite, metric, orientation or completeness assumption is built in.
H specifies allowed body relabelings; use the bottom subgroup for fixed labels.
G acts on C as the independently supplied allowed ACTIVE transformations.
Passive chart changes are bijective reencodings, handled separately.
-/

@[expose] public section
namespace TruthCore.Space.IdentityCriteria

/-- The supplied relational signature, including all its finite tuple data.
Whether these are complete physical data remains an independent open question. -/
structure SpatialData (C B R : Type) where
  data : C → R → List B → Prop
  bodyRelabelings : Subgroup (Equiv.Perm B)

/-- Isomorphism of the supplied relations using only allowed body permutations.
This is a structural condition, not a supplied same-configuration flag. -/
def RelationalIdentity {C B R : Type} (s : SpatialData C B R) (x y : C) : Prop :=
  ∃ e : s.bodyRelabelings, ∀ r bs,
    s.data x r bs ↔ s.data y r (bs.map e.val)

/-- Equality of classes under the supplied group of active transformations. -/
def QuotientIdentity (G : Type) {C : Type} [Group G] [MulAction G C]
    (x y : C) : Prop :=
  Quotient.mk (MulAction.orbitRel G C) x = Quotient.mk (MulAction.orbitRel G C) y

/-- Literal equality in the supplied full representation carrier, at fixed
parameters, body identities, world and chart. No cross-world identity is implied. -/
def RepresentedIdentity {C : Type} (x y : C) : Prop := x = y

/-- Every allowed active transformation preserves all supplied data up to an
allowed body permutation; not assumed by the group-action laws. -/
def DataPreserved {G C B R : Type} [Group G] [MulAction G C]
    (s : SpatialData C B R) : Prop :=
  ∀ (g : G) (x : C), RelationalIdentity s (g • x) x

/-- Every relational isomorphism is realized by an allowed active transformation.
This completeness premise concerns the specified signature, not actual physics. -/
def OrbitComplete (G : Type) {C B R : Type} [Group G] [MulAction G C]
    (s : SpatialData C B R) : Prop :=
  ∀ x y, RelationalIdentity s x y → ∃ g : G, g • y = x

/-- No allowed active transformation changes a represented configuration.
This is much stronger than invariance of relational data. -/
def OrbitTrivial (G C : Type) [Group G] [MulAction G C] : Prop :=
  ∀ (g : G) (x : C), g • x = x

/-- Passive transport of all observations; it changes representation, not the
represented arrangement by an active transformation. -/
def reencode {C D B R : Type} (s : SpatialData C B R) (chart : C ≃ D) :
    SpatialData D B R where
  data d := s.data (chart.symm d)
  bodyRelabelings := s.bodyRelabelings

/-- Passive transport of the orbit equivalence relation, rather than applying a
member of G to an arrangement. -/
def ChartQuotientIdentity (G : Type) {C D : Type} [Group G] [MulAction G C]
    (chart : C ≃ D) (x y : D) : Prop :=
  Quotient.mk (Setoid.comap chart.symm (MulAction.orbitRel G C)) x =
    Quotient.mk (Setoid.comap chart.symm (MulAction.orbitRel G C)) y

/-- A finite separating control only: a marked body, with its unary marker
predicate on all finite tuples. Alikeness allows body permutations. -/
def marker : SpatialData Bool Bool Unit where
  data x _ bs := bs = [x]
  bodyRelabelings := ⊤

/-- The same marker data with fixed body identities. -/
def fixedMarker : SpatialData Bool Bool Unit where
  data x _ bs := bs = [x]
  bodyRelabelings := ⊥

/-- Smallest active transformation scope: only the identity permutation. -/
abbrev FixedTransforms := (⊥ : Subgroup (Equiv.Perm Bool))

/-- Explicit finite comparison scope, not a claim that these exhaust all
philosophically relevant identities. Choosing one constructor fixes one test. -/
inductive Criterion where
  | relational | quotient | represented

def SelectedIdentity (G : Type) {C B R : Type} [Group G] [MulAction G C]
    (s : SpatialData C B R) (k : Criterion) (x y : C) : Prop :=
  match k with
  | .relational => RelationalIdentity s x y
  | .quotient => QuotientIdentity G x y
  | .represented => RepresentedIdentity x y

/-- All three criteria are compared on the same parameters in each general
clause. Controls are abstract marker models, not original spatial semantics. -/
def Certificate : Prop :=
  (∀ (G C B R : Type) [Group G] [MulAction G C] (s : SpatialData C B R) x y,
    RepresentedIdentity x y → QuotientIdentity G x y ∧ RelationalIdentity s x y) ∧
  (∀ (G C B R : Type) [Group G] [MulAction G C] (s : SpatialData C B R),
    DataPreserved (G := G) s → ∀ x y, QuotientIdentity G x y → RelationalIdentity s x y) ∧
  (∀ (G C B R : Type) [Group G] [MulAction G C] (s : SpatialData C B R),
    OrbitComplete G s → ∀ x y, RelationalIdentity s x y → QuotientIdentity G x y) ∧
  (∀ (G C B R : Type) [Group G] [MulAction G C] (s : SpatialData C B R),
    DataPreserved (G := G) s → OrbitComplete G s → OrbitTrivial G C →
      ∀ x y, (RelationalIdentity s x y ↔ QuotientIdentity G x y) ∧
        (QuotientIdentity G x y ↔ RepresentedIdentity x y) ∧
        (∀ k, SelectedIdentity G s k x y ↔ RepresentedIdentity x y)) ∧
  (∀ (G C D B R : Type) [Group G] [MulAction G C] (s : SpatialData C B R)
      (chart : C ≃ D) x y,
    (RelationalIdentity (reencode s chart) (chart x) (chart y) ↔ RelationalIdentity s x y) ∧
    (ChartQuotientIdentity G chart (chart x) (chart y) ↔ QuotientIdentity G x y) ∧
    (RepresentedIdentity (chart x) (chart y) ↔ RepresentedIdentity x y)) ∧
  (DataPreserved (G := FixedTransforms) marker ∧
    RelationalIdentity marker false true ∧ ¬ QuotientIdentity FixedTransforms false true) ∧
  (DataPreserved (G := Equiv.Perm Bool) marker ∧
    OrbitComplete (Equiv.Perm Bool) marker ∧
    QuotientIdentity (Equiv.Perm Bool) false true ∧ ¬ RepresentedIdentity false true) ∧
  (OrbitComplete (Equiv.Perm Bool) fixedMarker ∧
    QuotientIdentity (Equiv.Perm Bool) false true ∧ ¬ RelationalIdentity fixedMarker false true) ∧
  (DataPreserved (G := FixedTransforms) fixedMarker ∧
    OrbitComplete FixedTransforms fixedMarker ∧ OrbitTrivial FixedTransforms Bool ∧
    RepresentedIdentity false false ∧ RelationalIdentity fixedMarker false false ∧
    QuotientIdentity FixedTransforms false false)

end TruthCore.Space.IdentityCriteria
