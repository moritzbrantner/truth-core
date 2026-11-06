module

public import TruthCore.Case.Catholicism.StageThree.FoundingWeakScope

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingWeakScope
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.FoundingWeakScope

theorem explicitBodiesScopeCountermodel : ExplicitBodiesScopeCountermodel := by
  refine ⟨restrictedSig, restrictedAgency, true, false,
    ⟨true, rfl⟩, ?_, ?_, ⟨trivial, trivial⟩, ⟨true, trivial, trivial⟩,
    ?_, ?_, ?_, ?_, rfl, trivial, trivial, trivial, Bool.false_ne_true,
    trivial, trivial, Bool.false_ne_true, ?_, ?_, ?_⟩
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _ _ _ _ _; trivial
  · intro _ _ _ _ h; exact h
  · intro _ _ _ _; exact ⟨rfl, rfl⟩
  · intro _ _ _ h _; exact h
  · intro h; exact Bool.false_ne_true
      (h true rfl trivial trivial trivial trivial false trivial trivial)
  · intro h; exact Bool.false_ne_true (h true trivial false trivial trivial).1
  · intro h; exact Bool.false_ne_true (h false trivial trivial)

end TruthCore.Results.Case.Catholicism.StageThree.FoundingWeakScope
