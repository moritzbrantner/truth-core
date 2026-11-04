import TruthCore.Explanation.MechanismInterventionParity
import TruthCore.Results.Explanation.CompleteResponseParity.Solution

namespace TruthCore.Results.Explanation.MechanismInterventionParity

open TruthCore.Explanation.MechanismInterventionParity
open TruthCore.Modern.Hume.Regularity
set_option autoImplicit false

theorem unpack_pack : ∀ s : TwoState, unpack (pack s) = s := by
  intro s
  cases s
  rfl

theorem pack_unpack : ∀ s : OneState, pack (unpack s) = s := by
  intro s
  cases s
  rfl

/-- Public surgery cannot distinguish a pair-state stored in ONE slot from
the same two independently identified root-state slots. -/
theorem surgical_parity : ∀ s i, singleRun (pack s) i = pluralRun s i := by
  intro s i
  cases s
  rfl

theorem natural_agreement : NaturalAgreement := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · change (s.first = true ↔ s.first = true)
    exact Iff.rfl
  · change (s.second = true ↔ s.second = true)
    exact Iff.rfl
  · rcases s with ⟨a, b⟩
    cases a <;> cases b <;> decide

/-- Unlike mere matching observations, the supplied AND equation responds
when either publicly set contributor changes with the other held on. -/
theorem plural_sensitive : RespondsToEitherInput pluralRun := by
  constructor
  · refine ⟨false, ?_⟩
    change false ≠ true
    decide
  · refine ⟨false, ?_⟩
    change false ≠ true
    decide

theorem single_sensitive :
    RespondsToEitherInput (fun s i => singleRun (pack s) i) := by
  constructor
  · refine ⟨false, ?_⟩
    change false ≠ true
    decide
  · refine ⟨false, ?_⟩
    change false ≠ true
    decide

/-- The idle lookup reads the unmodified background directly. Its effect
ignores both public overrides, despite identical natural observations. -/
theorem idle_not_sensitive : ¬ RespondsToEitherInput idleRun := by
  rintro ⟨⟨u, hu⟩, _⟩
  change (u && true) ≠ (u && true) at hu
  exact hu rfl

theorem surgery_exposes_idle : ∃ s i, pluralRun s i ≠ idleRun s i := by
  refine ⟨⟨false, true⟩, ⟨some true, some true⟩, ?_⟩
  change (⟨true, true, true⟩ : Observation) ≠ ⟨true, true, false⟩
  decide

/-- A single Boolean source cannot realize three pairwise different public
responses, let alone all four. This is a cardinality limit on STATE, not a
claim that a metaphysically single bearer must have only two states. -/
theorem capacity_fork : CapacityFork := by
  constructor
  · intro a b
    exact ⟨(a, b), rfl, rfl⟩
  · intro a b hall
    rcases hall false false with ⟨u, hua, hub⟩
    rcases hall false true with ⟨v, hva, hvb⟩
    rcases hall true false with ⟨w, hwa, hwb⟩
    cases u <;> cases v <;> cases w <;> simp_all

theorem certificate : TruthCore.Explanation.MechanismInterventionParity.Certificate :=
  ⟨unpack_pack, pack_unpack, surgical_parity, natural_agreement,
    plural_sensitive, single_sensitive, idle_not_sensitive,
    surgery_exposes_idle, capacity_fork,
    TruthCore.Results.Explanation.CompleteResponseParity.root_parity⟩

end TruthCore.Results.Explanation.MechanismInterventionParity
