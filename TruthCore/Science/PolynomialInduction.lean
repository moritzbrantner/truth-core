module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Polynomial.Basic
@[expose] public section
namespace TruthCore.Science.PolynomialInduction
open Polynomial
/-- Exact coefficient-model identifiability, not existence or physical truth.
A Finset encodes distinct observed inputs. Zero is included via natDegree. -/
def Identifiable {K : Type*} [CommRing K] [IsDomain K] (s : Finset K) (d : ℕ) : Prop :=
  ∀ p q : K[X], p.natDegree ≤ d → q.natDegree ≤ d →
    (∀ x ∈ s, p.eval x = q.eval x) → p = q
/-- Monic observation-vanishing polynomial; the empty product is one. -/
noncomputable def vanishing {K : Type*} [CommRing K] (s : Finset K) : K[X] :=
  ∏ x ∈ s, (X - C x)
/-- Analyst conditional mathematics. No actual law or measurement warrant. -/
def Certificate : Prop :=
  (∀ (K : Type) [CommRing K] [IsDomain K] (s : Finset K) (d : ℕ),
    Identifiable s d ↔ d < s.card) ∧
  (∀ (K : Type) [CommRing K] [IsDomain K] (s : Finset K) (a : K), a ∉ s →
    ∀ p : K[X], (∀ x ∈ s, (p + vanishing s).eval x = p.eval x) ∧
      (p + vanishing s).eval a ≠ p.eval a) ∧
  (∀ (K : Type) [CommRing K] [IsDomain K] (p : K[X]) (a b : K), a ≠ 0 →
    (p.comp (C a * X + C b)).natDegree = p.natDegree) ∧
  ((∀ x ∈ ({0,1,2,3} : Finset ℚ),
    (X^2 + X*(X-1)*(X-2)*(X-3) : ℚ[X]).eval x = (X^2 : ℚ[X]).eval x) ∧
    (X^2 : ℚ[X]).eval 4 = 16 ∧
    (X^2 + X*(X-1)*(X-2)*(X-3) : ℚ[X]).eval 4 = 40) ∧
  (Function.Bijective (fun x : ℝ => x+x^3) ∧
    (X+X^3 : ℝ[X]).natDegree = 3 ∧ (X : ℝ[X]).natDegree = 1)
end TruthCore.Science.PolynomialInduction
