import Mathlib.Tactic

namespace TruthCore.Politics.DistrictMajority

/-- Stipulative two-party ballot profile: three districts, each with three distinct
voters. Each Boolean ballot is counted once. This is an independent aggregation
test motivated by Carneades.org, “What is Democracy?”, 04:24–04:48; it is not
a sourced formalization or a model of consent, rights, or moral authority. -/
abbrev Profile := Fin 3 → Fin 3 → Bool

/-- Number of A ballots among three voters. Finite enumeration, not a new notion
of cardinality; the explicit size-three formula keeps the fixture transparent. -/
def count (v : Fin 3 → Bool) : Nat :=
  (v 0).toNat + (v 1).toNat + (v 2).toNat

def localCount (p : Profile) (d : Fin 3) : Nat := count (p d)
def popularCount (p : Profile) : Nat := localCount p 0 + localCount p 1 + localCount p 2
def popularWin (p : Profile) : Prop := 5 ≤ popularCount p
def districtWin (p : Profile) : Prop :=
  2 ≤ count (fun d => decide (2 ≤ localCount p d))

/-- Five A voters packed as 3,1,1. B wins the other two districts 2–1. -/
def packed : Profile := fun d v => decide (d = 0 ∨ v = 0)

/-- Same five A voters redistributed as 2,2,1. No voter weights or district sizes
change; only which ballots are grouped together changes. -/
def spread : Profile := fun d v => decide ((d = 0 ∨ d = 1) ∧ v ≠ 2 ∨ d = 2 ∧ v = 0)

/-- Reversal witness, regrouping control, and unanimous A/B controls. The
conclusion is electoral only; there is no inference to a duty to obey or resist. -/
def Certificate : Prop :=
  popularCount packed = 5 ∧ popularWin packed ∧ ¬ districtWin packed ∧
  popularCount spread = 5 ∧ districtWin spread ∧
  (∀ p : Profile, (∀ d v, p d v = true) → popularWin p ∧ districtWin p) ∧
  (∀ p : Profile, (∀ d v, p d v = false) → ¬ popularWin p ∧ ¬ districtWin p)

end TruthCore.Politics.DistrictMajority
