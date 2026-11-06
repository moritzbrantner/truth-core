module

public import TruthCore.Metaethics.EvilObjection
public import TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore.Solution

@[expose] public section

namespace TruthCore.Results.Metaethics.EvilObjection.InternalChallenge

open TruthCore.Metaethics.EvilObjection TruthCore.English.OConnor TruthCore.English.Rowe TruthCore.Logic

theorem internalPermissionChallenge (s : Sig)
    (hGratuitous : GratuitousSufferingReading s) : InternalPermissionChallenge s := by
  intro hTheism hPermission
  exact TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore.roweDeductiveCore
    s hGratuitous hPermission hTheism

end TruthCore.Results.Metaethics.EvilObjection.InternalChallenge
