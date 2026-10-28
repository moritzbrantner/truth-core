import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Stipulated finite population arithmetic, prompted by provisional Carneades
caption reading zG814I1DBzU 00:31–03:24 and 06:43–07:52. No historical source
claim is encoded. Means use an assumed common cardinal interpersonal scale;
ordinal preference alone does not supply it. No empty or infinite population
is admitted. A profile records a mean, not each person's welfare. -/
namespace TruthCore.Ethics.PopulationAggregation

/-- Finite nonempty population summary on a stipulated common real scale. -/
structure Profile where
  count : Nat
  nonempty : 0 < count
  mean : ℝ

/-- Arithmetic total; no claim that this is morally authoritative. -/
def Profile.total (p : Profile) : ℝ := (p.count : ℝ) * p.mean

/-- Strict ranking purely by total welfare. Arguments are worse, better. -/
def TotalRanking (r : Profile → Profile → Prop) : Prop :=
  ∀ p q, r p q ↔ p.total < q.total

/-- Rival strict ranking purely by average welfare, on the same scale. -/
def AverageRanking (r : Profile → Profile → Prop) : Prop :=
  ∀ p q, r p q ↔ p.mean < q.mean

/-- Arbitrarily small positive means can beat any higher-mean finite profile
in total with a sufficiently large finite count. Hence total and average strict
rankings cannot coincide globally. Equal-count comparisons do coincide; zero
mean cannot outrank positive total. None of this chooses a moral ranking or
establishes feasibility of arbitrary population growth. -/
def Controls : Prop :=
  (∀ (p : Profile) (ε : ℝ), 0 < ε → ε < p.mean →
    ∃ q : Profile, q.mean = ε ∧ p.count < q.count ∧ p.total < q.total) ∧
  (¬ ∃ r, TotalRanking r ∧ AverageRanking r) ∧
  (∀ p q : Profile, p.count = q.count →
    (p.total < q.total ↔ p.mean < q.mean)) ∧
  (∀ p q : Profile, 0 < p.total → q.mean = 0 → ¬ p.total < q.total)

end TruthCore.Ethics.PopulationAggregation
