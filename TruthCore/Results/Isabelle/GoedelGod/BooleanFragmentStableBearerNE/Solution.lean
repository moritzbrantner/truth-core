import TruthCore.Isabelle.AFP.GoedelGod.GeneratedFragment

namespace TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentStableBearerNE

open TruthCore.Isabelle.AFP.GoedelGod

theorem checks {World Ind : Type} : BooleanFragmentStableBearerNE World Ind := by
  intro F atom x hStable w Φ ⟨readout, hΦ⟩ hEss next _
  refine ⟨x, ?_⟩
  apply (hΦ x next).mpr
  rw [← hStable w next]
  exact (hΦ x w).mp hEss.1

end TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentStableBearerNE
