module
public import TruthCore.Explanation.EmptyTruthmaker
public import TruthCore.Results.Explanation.TruthmakerTheories.Solution
@[expose] public section
namespace TruthCore.Models.EmptyTruthmaker
open TruthCore.Explanation.EmptyTruthmaker
open TruthCore.Explanation.TruthmakerTheories
open TruthCore.Results.Explanation.TruthmakerTheories

theorem omitE_notE : ¬ EmptyPossible oneFrame (presentControl false) () := by
  rintro ⟨_, _, h⟩; exact h () rfl

theorem omitE_T : NegativeCoverage oneFrame (presentControl false) noMaker () := by
  intro _ _ he
  exact (negativeMap.2.2.1.2.1) ((negativeEmpty false).2 he)

theorem omitE_I : Immanence oneFrame (presentControl false) noMaker () := by
  intro _ _ b hb; exact hb.elim

theorem omitE_factive : NegativeFactivity oneFrame (presentControl false) noMaker () := by
  intro _ _ b hb; exact hb.elim

theorem omitT_E : EmptyPossible oneFrame (presentControl true) () := by
  exact ⟨(), trivial, (negativeEmpty true).1 negativeMap.2.2.2.1.1⟩

theorem omitT_notT : ¬ NegativeCoverage oneFrame (presentControl true) noMaker () := by
  intro ht
  exact negativeMap.2.2.2.1.2.2 (fun _ => ht () trivial ((negativeEmpty true).1 rfl))

theorem omitT_I : Immanence oneFrame (presentControl true) noMaker () := by
  intro _ _ b hb; exact hb.elim

theorem omitT_factive : NegativeFactivity oneFrame (presentControl true) noMaker () := by
  intro _ _ b hb; exact hb.elim

theorem omitI_E : EmptyPossible oneFrame (presentControl true) () := omitT_E

theorem omitI_T : NegativeCoverage oneFrame (presentControl true) absentMaking () := by
  intro _ _ he
  exact negativeMap.2.2.2.2.1.2.1 ((negativeEmpty true).2 he)

theorem omitI_notI : ¬ Immanence oneFrame (presentControl true) absentMaking () := by
  intro hi
  exact Bool.noConfusion (hi () trivial () ⟨rfl, rfl⟩)

theorem omitI_factive : NegativeFactivity oneFrame (presentControl true) absentMaking () := by
  intro _ _ b hb
  exact (negativeEmpty true).1 (negativeMap.2.2.2.2.1.2.2.1 true b .empty hb)
end TruthCore.Models.EmptyTruthmaker
