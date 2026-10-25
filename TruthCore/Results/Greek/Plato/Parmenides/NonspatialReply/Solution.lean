import TruthCore.Greek.Plato.Parmenides.ReplyModels
import TruthCore.Results.Comparison.PlatonicForms.SelfPredicatingConsistent.Solution
import TruthCore.Results.Greek.Plato.Parmenides.WholePartObjection.Solution
namespace TruthCore.Results.Greek.Plato.Parmenides.NonspatialReply
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges

theorem nonspatialReply : NonspatialPossible := by
  obtain ⟨s, hm, ho, hu, hp, hn, hs, he, _, _, _⟩ :=
    TruthCore.Results.Comparison.PlatonicForms.SelfPredicatingConsistent.selfPredicatingConsistent
  let m : Mereology (Fin 3) := ⟨fun _ _ => False, fun _ _ => False, fun _ _ => False⟩
  have hi : IndivisibleForms s m := by
    intro _ _ _ _ _ h
    exact h
  have hw : WholeExclusive m := by
    intro _ _ _ h
    exact False.elim h
  refine ⟨s, m, hm, ho, hu, hp, hn, hs, he, hi, hw, ?_⟩
  exact TruthCore.Results.Greek.Plato.Parmenides.WholePartObjection.wholePartObjection
    s m hm ho hw hi

end TruthCore.Results.Greek.Plato.Parmenides.NonspatialReply
