import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
namespace TruthCore.Results.Isabelle.NotesOnGoedel.EmptyPropertyIsEssence
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
/-- AFP `GoedelVariantHOML1.thy`, lemma `EmptyEssL`: in Gödel's 1970 variant
the empty property is an essence of every individual at every world, from the
definition `Essence` alone. -/
theorem emptyPropertyIsEssence {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) :
    EmptyPropertyIsEssence F ex := by
  sorry
end TruthCore.Results.Isabelle.NotesOnGoedel.EmptyPropertyIsEssence
