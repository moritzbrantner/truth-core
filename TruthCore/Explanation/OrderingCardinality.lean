module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import TruthCore.Explanation.HistorySelection

/-! #1003: count labeled arrangements, not unlabeled order types or metaphysical
possibilities. An arrangement enumerates the fixed labels Nat exactly once.
`earlier` is the transported strict order of type omega; reversing it gives the
ancestral order. `next` supplies an upstream predecessor at every label. These
are mathematical links, without an independently established causal meaning.
The same complete labeled links determine the arrangement, so permuting the
labels changes the whole chain rather than a further order over fixed links. -/

@[expose] public section

namespace TruthCore.Explanation.OrderingCardinality
open Cardinal
open TruthCore.Explanation.HistorySelection

abbrev Arrangement := Equiv.Perm Nat

/-- Position in the enumeration is order, not physical time. -/
def earlier (e : Arrangement) (x y : Nat) : Prop := e.symm x < e.symm y

/-- The immediately upstream label. It exists even at enumeration position 0. -/
def next (e : Arrangement) (x : Nat) : Nat := e (e.symm x + 1)

/-- One endpoint and the entire immediate-link function. The endpoint is a
terminal of the backward chain, not a source with no upstream predecessor. -/
def chainData (e : Arrangement) : Nat × (Nat → Nat) := (e 0, next e)

/-- A true proposition excludes every different labeled arrangement. This is
an entailing informational test, not a definition of adequate explanation. -/
def Selects (a : Arrangement) (p : Arrangement → Prop) : Prop :=
  p a ∧ ∀ e, p e → e = a

/-- OPEN local framework bridge: any candidate accepted as a complete
explanation of THIS actual chain must pass the entailing arrangement test.
`adequate` is a supplied judgment, not a disguised theorem or a causal relation.
Necessitating, probabilistic and intrinsic accounts disagree about this bridge. -/
def CompleteRequiresSelection (a : Arrangement)
    (adequate : (Arrangement → Prop) → Prop) : Prop :=
  ∀ p, adequate p → Selects a p

/-- OPEN rival to the local entailing demand: at least one accepted complete
explanation leaves another arrangement compatible with its candidate truth.
It does not assert that every uninformative token is adequate. -/
def AcceptsUnselected (a : Arrangement)
    (adequate : (Arrangement → Prop) → Prop) : Prop :=
  ∃ p, adequate p ∧ ¬ Selects a p

/-- These are propositions about the entire endpoint (indexed by Nat) as well
as links. They contain the arrangement's full information, not its warrant. -/
def FullTruth (e : Arrangement) (r : Nat × Option Nat) : Prop :=
  match r.2 with
  | none => e 0 = r.1
  | some x => next e x = r.1

/-- A completely specified finite recursive program, with no oracle for its
infinitely many values. Its mathematical applicability is not physical actuality. -/
def generated : Nat → Nat := Nat.rec 0 (fun _ value => value + 1)

/-- Closed R3 example: verify all generated values and every identity-chain
successor by a finite proof, without assuming a universal test outcome. -/
def FiniteRule : Prop :=
  ∀ n, generated n = n ∧ next (Equiv.refl Nat) n = n + 1

/-- The cardinal theorem includes injectivity into the transported labeled
strict orders, so it counts actual distinct relations, not duplicate encodings. -/
def Cardinality : Prop :=
  #(Arrangement) = 2 ^ aleph0 ∧
  aleph0 < #(Arrangement) ∧
  Function.Injective earlier ∧
  #(Set.range earlier) = 2 ^ aleph0

/-- R1 reconstructs the arrangement from the fixed endpoint and local links.
R2 has the same continuum of alternatives on an empty Unit dependency relation.
R3 reconstructs every position by ordinary induction from a seed and rule.
The informational controls distinguish a complete vector from constant truth;
neither is equated with independent explanatory adequacy. -/
def Controls : Prop :=
  Function.Injective chainData ∧
  (∀ e : Arrangement, (∀ x, ∃ y, y = next e x) ∧
    ¬ WellFounded (fun y x => y = next e x)) ∧
  (#(Nat → Bool) = 2 ^ aleph0 ∧
    WellFounded (fun (_ _ : Unit) => False)) ∧
  (∀ (e : Arrangement) (f : Nat → Nat),
    f 0 = e 0 → (∀ n, f (n + 1) = next e (f n)) → ∀ n, f n = e n) ∧
  (∀ a : Arrangement, ¬ ∃ p,
    EvidenceOnly (fun (_ : Arrangement) (_ : Unit) => True) (fun _ => True) p ∧
      Selects a p) ∧
  (∀ a : Arrangement, ∃ p,
    EvidenceOnly FullTruth (fun _ => True) p ∧ Selects a p)

end TruthCore.Explanation.OrderingCardinality
