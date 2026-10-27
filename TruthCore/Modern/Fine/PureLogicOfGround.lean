import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

/-!
# Kit Fine, *The Pure Logic of Ground* (2012), §2: the system PLG

Source: `FINE-PLG-1-2`, pp. 3–7 (*The Review of Symbolic Logic* 5 (2012)
1–25). Fine lays down structural rules for four ground-theoretic operators
over a nonempty set of atomic truths, prescinding from their internal
structure:

| | strict | weak |
| --- | --- | --- |
| full | `Δ < C` | `Δ ≤ C` |
| partial | `A ≺ C` | `A ≼ C` |

Here `Δ` is a set of atoms, possibly empty or infinite (p. 5). This module
encodes the sequents and Fine's derivability relation `S ⊢_PLG s` (p. 6: the
least set of sequents containing `S` and closed under the rules) as an
inductive predicate, rule for rule as displayed on p. 5. Nothing here asserts
that any sequent is true of actual ground; the atoms are uninterpreted.

Encoding choices (`DEF-FINE-PLG-DERIVABILITY`):

* `Cut(≤/≤)` is indexed by a family `i ↦ (Δᵢ, Aᵢ)`, so the same atom may occur
  twice among `A₁, A₂, …` with different grounds. Fine's own derivation of
  Amalgamation uses exactly this (`C, C, … ≤ C`, p. 7).
* The subsumption rules from full to partial ground read `Δ, A < C` as
  "`A ∈ Δ` and `Δ < C`", which is the same since `Δ, A` abbreviates `Δ ∪ {A}`.
* `Reverse Subsumption` ranges over all antecedents of a set, so it is stated
  for the set directly.
* `Non-Circularity(≺)` concludes `⊥`, which Fine says "is used to indicate that
  any sequent whatever can be derived from the premise sequent" (p. 6): here
  `A ≺ A` derives every sequent.

Only the rules are encoded. Fine's fact semantics (§3) and his soundness and
completeness theorems are not formalized here (#349).
-/

namespace TruthCore.Modern.Fine.PureLogicOfGround

/-- A PLG sequent over atoms (p. 5): weak full `Δ ≤ C`, weak partial `A ≼ C`,
strict full `Δ < C` and strict partial `A ≺ C`. A sequent is a syntactic
object, not an assertion that the ground obtains. -/
inductive Sequent (Atom : Type) : Type
  | weakFull (antecedents : Set Atom) (consequent : Atom)
  | weakPartial (antecedent consequent : Atom)
  | strictFull (antecedents : Set Atom) (consequent : Atom)
  | strictPartial (antecedent consequent : Atom)

open Sequent

/-- `Derivable S s`: the sequent `s` is derivable from the set `S` of sequents
in Fine's system PLG (p. 5–6), i.e. it lies in every set containing `S` and
closed under the rules below. -/
inductive Derivable {Atom : Type} (S : Set (Sequent Atom)) : Sequent Atom → Prop
  /-- Members of `S` are derivable from `S`. -/
  | assumption {s : Sequent Atom} : s ∈ S → Derivable S s
  /-- Subsumption `(</≤)`: strict full ground is weak full ground. -/
  | subsumptionStrictFull {Δ : Set Atom} {C : Atom} :
      Derivable S (strictFull Δ C) → Derivable S (weakFull Δ C)
  /-- Subsumption `(≺/≼)`: strict partial ground is weak partial ground. -/
  | subsumptionStrictPartial {A C : Atom} :
      Derivable S (strictPartial A C) → Derivable S (weakPartial A C)
  /-- Subsumption `(</≺)`: each antecedent of a strict full ground is a
  strict partial ground. -/
  | subsumptionStrictFullPartial {Δ : Set Atom} {A C : Atom} :
      Derivable S (strictFull Δ C) → A ∈ Δ → Derivable S (strictPartial A C)
  /-- Subsumption `(≤/≼)`: each antecedent of a weak full ground is a weak
  partial ground. -/
  | subsumptionWeakFullPartial {Δ : Set Atom} {A C : Atom} :
      Derivable S (weakFull Δ C) → A ∈ Δ → Derivable S (weakPartial A C)
  /-- `Cut(≤/≤)`: from `Δᵢ ≤ Aᵢ` for every index and `A₁, A₂, … ≤ C`, infer
  `Δ₁, Δ₂, … ≤ C`. -/
  | cut {ι : Type} (A : ι → Atom) (Δ : ι → Set Atom) {C : Atom} :
      (∀ i, Derivable S (weakFull (Δ i) (A i))) →
        Derivable S (weakFull (Set.range A) C) →
          Derivable S (weakFull (⋃ i, Δ i) C)
  /-- Transitivity `(≼/≼)`. -/
  | transWeakWeak {A B C : Atom} :
      Derivable S (weakPartial A B) → Derivable S (weakPartial B C) →
        Derivable S (weakPartial A C)
  /-- Transitivity `(≼/≺)`. -/
  | transWeakStrict {A B C : Atom} :
      Derivable S (weakPartial A B) → Derivable S (strictPartial B C) →
        Derivable S (strictPartial A C)
  /-- Transitivity `(≺/≼)`. -/
  | transStrictWeak {A B C : Atom} :
      Derivable S (strictPartial A B) → Derivable S (weakPartial B C) →
        Derivable S (strictPartial A C)
  /-- Identity `(≤)`: `A ≤ A`, from no premises. -/
  | identity (A : Atom) : Derivable S (weakFull {A} A)
  /-- Non-Circularity `(≺)`: from `A ≺ A`, any sequent whatever. -/
  | nonCircularity {A : Atom} (s : Sequent Atom) :
      Derivable S (strictPartial A A) → Derivable S s
  /-- Reverse Subsumption `(≤/≺)`: a weak full ground all of whose antecedents
  are strict partial grounds of `C` is a strict full ground of `C`. -/
  | reverseSubsumption {Δ : Set Atom} {C : Atom} :
      Derivable S (weakFull Δ C) → (∀ A ∈ Δ, Derivable S (strictPartial A C)) →
        Derivable S (strictFull Δ C)

/-- `StrictlyGrounds S A C`: the strict partial ground `A ≺ C` is derivable
from `S` in PLG. Read as a relation from ground to grounded, so descending
along it moves to grounds. -/
def StrictlyGrounds {Atom : Type} (S : Set (Sequent Atom)) (A C : Atom) : Prop :=
  Derivable S (strictPartial A C)

/-- `S` is PLG-consistent: some sequent is not derivable from it. By
Non-Circularity, an inconsistent `S` derives every sequent. -/
def Consistent {Atom : Type} (S : Set (Sequent Atom)) : Prop :=
  ∃ s, ¬ Derivable S s

/-- Fine's claim (p. 6–7) that the following rules are derivable in PLG, for
every atom type and every set of assumed sequents:

* Transitivity `(≺/≺)`: `A ≺ B` and `B ≺ C` give `A ≺ C`;
* Amalgamation `(≤)`: from `Δᵢ ≤ C` for each member of a nonempty family,
  `⋃ Δᵢ ≤ C`;
* Amalgamation `(<)`: from `Δᵢ < C` for each member of a nonempty family,
  `⋃ Δᵢ < C`.

Fine displays both amalgamation rules with at least one premise
(`Δ₁ ≤ C Δ₂ ≤ C …`); the nonemptiness hypothesis records that, since his
derivation cuts against `C, C, … ≤ C`, whose antecedent set is `{C}` only for a
nonempty family. -/
def PlgDerivedRules : Prop :=
  ∀ (Atom : Type) (S : Set (Sequent Atom)),
    (∀ A B C : Atom, StrictlyGrounds S A B → StrictlyGrounds S B C →
        StrictlyGrounds S A C) ∧
    (∀ (ι : Type) (_ : Nonempty ι) (Δ : ι → Set Atom) (C : Atom),
        (∀ i, Derivable S (weakFull (Δ i) C)) → Derivable S (weakFull (⋃ i, Δ i) C)) ∧
    (∀ (ι : Type) (_ : Nonempty ι) (Δ : ι → Set Atom) (C : Atom),
        (∀ i, Derivable S (strictFull (Δ i) C)) → Derivable S (strictFull (⋃ i, Δ i) C))

/-- For every atom type and every PLG-consistent set `S` of assumed sequents:

* no atom is a derivable strict ground of itself through any finite chain of
  derivable strict partial grounds (no derivable cycle of any length
  `A ≺ … ≺ A`, via Mathlib's `Relation.TransGen`);
* no derivable strict partial ground `A ≺ B` is reversed by a derivable weak
  partial ground `B ≼ A`; and
* if there are only finitely many atoms, derivable strict partial ground is
  well-founded: there is no infinite descent along it.

This is about derivability in PLG from `S`, not about the actual ground
relation; it does not assert that `S` is consistent. -/
def ConsistentStrictGroundAcyclic : Prop :=
  ∀ (Atom : Type) (S : Set (Sequent Atom)), Consistent S →
    (∀ A, ¬ Relation.TransGen (StrictlyGrounds S) A A) ∧
    (∀ A B, StrictlyGrounds S A B → ¬ Derivable S (weakPartial B A)) ∧
    (Finite Atom → WellFounded (StrictlyGrounds S))

/-- There is a PLG-consistent set of sequents over the natural numbers from
which `n + 1 ≺ n` is derivable for every `n`, so derivable strict partial
ground is not well-founded. Non-Circularity and the other PLG rules therefore
exclude cycles of strict ground without excluding infinite descending chains
of strict ground. -/
def NonCircularityAllowsInfiniteDescent : Prop :=
  ∃ S : Set (Sequent Nat), Consistent S ∧
    (∀ n, StrictlyGrounds S (n + 1) n) ∧
    ¬ WellFounded (StrictlyGrounds S)

end TruthCore.Modern.Fine.PureLogicOfGround
