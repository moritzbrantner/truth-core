import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Isabelle.GoedelGod.GodLikeNecessarilyExists.Solution
namespace TruthCore.Results.Isabelle.GoedelGod.ModalCollapse
open TruthCore.Modal (Frame Symmetric)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Isabelle.AFP.GoedelGod
open TruthCore.Results.Isabelle.GoedelGod.GodLikeNecessarilyExists
  (positivePossiblyExemplified godLikePossiblyExists godLikeIsEssence
    godLikeNecessarilyExists)

/-- AFP corollary `C2` (`by (metis T1 T3 G_def sym)`): a God-like being exists
at every world, without reflexivity. By `C` some world `v` accessible from `w`
has a God-like being; by `T3` at `v`, and symmetry, a God-like being exists at
`w`. -/
theorem godLikeActuallyExists {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hC : GodLikePossiblyExists F P)
    (hT3 : GodLikeNecessarilyExists F P)
    (hSym : Symmetric F) :
    GodLikeActuallyExists P := by
  intro w
  obtain ⟨v, hWV, _⟩ := hC w
  exact hT3 v w (hSym w v hWV)

/-- Modal collapse. Let `φ` hold at `w`, and let `v` be accessible from `w`.
A God-like `x` exists at `w` (`C2`). Being God-like is an essence of `x` at `w`
(`T2`), and `x` has at `w` the property `fun _ => φ` (every individual has it
there, since `φ` holds at `w`). So at `v` everything God-like has that
property, that is, `φ` holds at `v` if anything God-like exists at `v`; and a
God-like being exists at `v` (`T3`). The proof uses the full comprehension of
the embedding: `fun _ => φ` is a property. -/
theorem modalCollapse {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hA1a : NegationPositiveExcludesPositive P)
    (hA1b : NonPositiveHasPositiveNegation P)
    (hA2 : PositiveClosedUnderNecessaryImplication F P)
    (hA3 : GodLikePositive P)
    (hA4 : PositiveNecessarilyPositive F P)
    (hA5 : NecessaryExistencePositive F P)
    (hSym : Symmetric F)
    (hEM : ExcludedMiddle) :
    ModalCollapse F := by
  have hC := godLikePossiblyExists F P (positivePossiblyExemplified F P hA1a hA2 hEM) hA3
  have hT2 := godLikeIsEssence F P hA1b hA4 hEM
  have hT3 := godLikeNecessarilyExists F P hA1a hA1b hA2 hA3 hA4 hA5 hSym hEM
  intro w φ hφ v hWV
  obtain ⟨x, hGodLike⟩ := godLikeActuallyExists F P hC hT3 hSym w
  obtain ⟨y, hGodLikeY⟩ := hT3 w v hWV
  exact (hT2 w x hGodLike).2 (fun _ => φ) hφ v hWV y hGodLikeY
end TruthCore.Results.Isabelle.GoedelGod.ModalCollapse
