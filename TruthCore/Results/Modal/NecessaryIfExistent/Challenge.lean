import TruthCore.Modal.NecessaryIfExistent
namespace TruthCore.Results.Modal.NecessaryIfExistent
open TruthCore.Modal TruthCore.Modal.NecessaryIfExistent

theorem positive {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) (hp : PossibleExistence F G w) :
    NecessaryExistence F G w := by sorry

theorem negative {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) (hp : PossibleNonexistence F G w) :
    ImpossibleExistence F G w := by sorry

theorem coverage {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w)
    (hem : TruthCore.Logic.ExcludedMiddle) : Coverage F G w := by sorry

theorem controls : Controls := by sorry
end TruthCore.Results.Modal.NecessaryIfExistent
