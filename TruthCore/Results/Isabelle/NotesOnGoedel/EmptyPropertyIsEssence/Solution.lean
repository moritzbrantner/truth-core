import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
namespace TruthCore.Results.Isabelle.NotesOnGoedel.EmptyPropertyIsEssence
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1

/-- AFP `EmptyEssL` (`using Essence_def by auto`). Whatever `x` has, every
existing individual that has the empty property has it, vacuously, since
nothing has the empty property. Gödel's 1970 essence does not require `x` to
have its essence, so nothing excludes the empty property. -/
theorem emptyPropertyIsEssence {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) :
    EmptyPropertyIsEssence F ex := by
  intro _ _ _ _ _ _ _ _ hFalse
  exact hFalse.elim
end TruthCore.Results.Isabelle.NotesOnGoedel.EmptyPropertyIsEssence
