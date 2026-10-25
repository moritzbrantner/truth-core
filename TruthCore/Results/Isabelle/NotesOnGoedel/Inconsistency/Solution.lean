import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
import TruthCore.Results.Isabelle.NotesOnGoedel.EmptyPropertyIsEssence.Solution
namespace TruthCore.Results.Isabelle.NotesOnGoedel.Inconsistency
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
open TruthCore.Results.Isabelle.NotesOnGoedel.EmptyPropertyIsEssence
  (emptyPropertyIsEssence)

/-- AFP proof of `Inconsistency`, step 1 (`using Ax2a Ax4 by blast`). If the
empty property were positive, its negation would be too (`Ax4`: the empty
property is vacuously included in every property), and `Ax2a` forbids a
property and its negation both being positive. -/
theorem emptyPropertyNotPositive {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx4 : PositiveClosedUnderNecessaryInclusion F ex P) :
    EmptyPropertyNotPositive P := by
  intro w hEmpty
  have hNegation : P (fun x v => ¬ (fun (_ : Ind) (_ : World) => False) x v) w :=
    hAx4 w _ _ hEmpty (fun _ _ _ _ hFalse => hFalse.elim)
  exact (hAx2a w (fun _ _ => False)).2 ⟨hEmpty, hNegation⟩

/-- No world is a dead end. At a dead end every necessity holds vacuously, so
the negation of the empty property (positive by `Ax2a`, since the empty
property is not) would be necessarily included in the empty property, and the
empty property would be positive (`Ax4`). -/
theorem noDeadEndWorld {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx4 : PositiveClosedUnderNecessaryInclusion F ex P)
    (hNotEmpty : EmptyPropertyNotPositive P) :
    NoDeadEndWorld F := by
  intro w hDeadEnd
  rcases (hAx2a w (fun _ _ => False)).1 with hEmpty | hNegation
  · exact hNotEmpty w hEmpty
  · exact hNotEmpty w
      (hAx4 w _ _ hNegation (fun v hAccess _ _ _ => (hDeadEnd v hAccess).elim))

/-- AFP theorem `Inconsistency: False` (sledgehammer from `Ax2a Ax3 Ax4
EmptyEssL NecExist_def`). Take any world `w`. Necessary existence is positive
there (`Ax3`). It is necessarily included in the empty property: at any world
`v` accessible from `w`, an individual that exists necessarily has the empty
property as an essence (`EmptyEssL`), so the empty property is exemplified at
every world accessible from `v`, so no world is accessible from `v`, which
contradicts `noDeadEndWorld`. By `Ax4` the empty property is positive at `w`,
which contradicts `emptyPropertyNotPositive`. So there is no world. No frame
condition is used: the theory's S5 axioms `Rrefl`, `Rsymm`, `Rtrans` are not
needed, nor are `Ax1` and `Ax2b`. -/
theorem inconsistency {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx3 : NecessaryExistencePositive F ex P)
    (hAx4 : PositiveClosedUnderNecessaryInclusion F ex P) :
    NoWorld World := by
  intro w
  have hNotEmpty := emptyPropertyNotPositive F ex P hAx2a hAx4
  have hNoDeadEnd := noDeadEndWorld F ex P hAx2a hAx4 hNotEmpty
  have hEmptyEssence := emptyPropertyIsEssence F ex
  apply hNotEmpty w
  apply hAx4 w (NecessaryExistence F ex) _ (hAx3 w)
  intro v _ y _ hNecessary
  exact hNoDeadEnd v fun t hAccess =>
    Exists.elim (hNecessary _ (hEmptyEssence v y) t hAccess) fun _ hz => hz.2
end TruthCore.Results.Isabelle.NotesOnGoedel.Inconsistency
