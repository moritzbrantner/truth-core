import TruthCore.Isabelle.AFP.GoedelGod

namespace TruthCore.Results.Isabelle.GoedelGod.FullFilterRecoversScott

open TruthCore.Isabelle.AFP.GoedelGod

/-- The unrestricted filter is conservative: its additional `True` arguments
do not change the meaning of either nested property quantifier. -/
theorem checks {World Ind : Type} : FullFilterRecoversScott World Ind := by
  intro F x w
  constructor
  · intro hFull Φ hEss next hAccess
    apply hFull Φ trivial ⟨hEss.1, ?_⟩ next hAccess
    intro Ψ _ hΨ
    exact hEss.2 Ψ hΨ
  · intro hScott Φ _ hEss next hAccess
    apply hScott Φ ⟨hEss.1, ?_⟩ next hAccess
    intro Ψ hΨ
    exact hEss.2 Ψ trivial hΨ

end TruthCore.Results.Isabelle.GoedelGod.FullFilterRecoversScott
