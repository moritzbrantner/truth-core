import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Isabelle.GoedelGod.GodLikeUnique
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Isabelle.AFP.GoedelGod
/-- AFP `GoedelGod.thy`, theorem `Monotheism`: any two God-like beings at a
world have the same properties there (Leibniz indiscernibility), from axiom
`A1b` and excluded middle. No frame condition and no other axiom is used. -/
theorem godLikeUnique {World : Type} {Ind : Type}
    (P : Positivity World Ind)
    (hA1b : NonPositiveHasPositiveNegation P)
    (hEM : ExcludedMiddle) :
    GodLikeUnique P := by
  sorry
end TruthCore.Results.Isabelle.GoedelGod.GodLikeUnique
