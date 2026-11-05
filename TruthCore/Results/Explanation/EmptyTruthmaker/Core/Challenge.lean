import TruthCore.Explanation.EmptyTruthmaker
namespace TruthCore.Results.Explanation.EmptyTruthmaker.Core
open TruthCore.Explanation.EmptyTruthmaker
 theorem incompatible (W B : Type) (F : TruthCore.Modal.Frame W)
    (present makes : W → B → Prop) (a : W)
    (hE : EmptyPossible F present a) (hT : NegativeCoverage F present makes a)
    (hI : Immanence F present makes a) : TruthCore.Logic.ConfigurationFalse := by sorry
end TruthCore.Results.Explanation.EmptyTruthmaker.Core
