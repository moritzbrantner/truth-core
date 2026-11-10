module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped BigOperators
namespace TruthCore.Causality.QuantitativeTransferPaths
def Path {V : Type} (w : V → V → ℝ) := Relation.ReflTransGen (fun v u => 0 < w v u)

def FinitePath : Prop :=
  ∀ {V : Type} [Countable V] (w : V → V → ℝ) (s P : V → ℝ)
    (q M : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hw : ∀ v u, 0 ≤ w v u) (hs : ∀ v, 0 ≤ s v)
    (_hP : ∀ v, 0 ≤ P v) (hbound : ∀ v, P v ≤ M)
    (hsum : ∀ v, Summable (w v)) (hrow : ∀ v, ∑' u, w v u ≤ q)
    (hprod : ∀ v, Summable (fun u => w v u * P u))
    (hbal : ∀ v, P v ≤ s v + ∑' u, w v u * P u)
    (v : V) (hv : 0 < P v),
  ∃ u, Path w v u ∧ 0 < s u

def VanishingTail : Prop :=
  ∀ (P q : ℕ → ℝ) (M : ℝ)
    (hq : ∀ n, 0 ≤ q n) (hbound : ∀ n, |P n| ≤ M)
    (hbal : ∀ n, P n = q n * P (n+1))
    (htail : ∀ n, Filter.Tendsto
      (fun k => ∏ j ∈ Finset.range k, q (n+j)) Filter.atTop (nhds 0)),
  ∀ n, P n = 0

def binary (P : List Bool → ℝ) (v : List Bool) :=
  (1/2)*P (false :: v) + (1/2)*P (true :: v)

def chainQ (n : ℕ) : ℝ := 1 - 1/((n : ℝ)+2)^2

def chainP (n : ℕ) : ℝ := ((n : ℝ)+1)/((n : ℝ)+2)

def nonuniform (P : ℕ → ℝ) (n : ℕ) := chainQ n * P (n+1)

def halfChain (P : ℕ → ℝ) (n : ℕ) := (1/2)*P (n+1)

def BinaryFixed : Prop :=
  binary (fun _ => 1) = (fun _ => 1) ∧
    binary (fun _ => 0) = (fun _ => 0) ∧
    (∀ v : List Bool, false :: v ≠ true :: v)

def NonuniformFixed : Prop :=
  nonuniform chainP = chainP ∧
    (∀ n, 0 < chainP n ∧ chainP n ≤ 1 ∧ 0 < chainQ n ∧ chainQ n < 1)

def HalfFixed : Prop :=
  halfChain (fun n => (2 : ℝ)^n) = (fun n => (2 : ℝ)^n) ∧
    (∀ M : ℝ, ∃ n, M < (2 : ℝ)^n)

def NonuniformTail : Prop :=
  ∀ n k,
    chainP n ≤ ∏ j ∈ Finset.range k, chainQ (n+j)

def ResourceBudget : Prop :=
  ∀ {C R : Type} (consumers : Finset C) (resources : Finset R)
    (a : C → R → ℝ) (b : R → ℝ) (hb : ∀ r ∈ resources, 0 ≤ b r)
    (ha : ∀ r ∈ resources, ∑ c ∈ consumers, a c r ≤ 1),
  ∑ c ∈ consumers, ∑ r ∈ resources, a c r * b r ≤ ∑ r ∈ resources, b r

def ConservativeCircle : Prop :=
  (∀ v : Bool, (1 : ℝ) = (fun _ : Bool => (1 : ℝ)) (!v)) ∧
    (∑ v : Bool, (1 : ℝ)) = 2
end TruthCore.Causality.QuantitativeTransferPaths
