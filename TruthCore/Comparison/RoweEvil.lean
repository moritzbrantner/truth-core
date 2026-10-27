import TruthCore.English.Rowe.EvidentialEvil

namespace TruthCore.Comparison.RoweEvil
open TruthCore.English.Rowe

/-- An interpretation satisfying the permission constraint, apparent
pointlessness, narrow theism, and absence of actual gratuitous suffering.
This tests a deductive inference from appearance alone, not the evidential
strength of Rowe's variety/profusion argument or actual divine permission. -/
def ApparentCompatibility : Prop :=
  ∃ s : Sig, PermissionConstraintReading s ∧ ApparentlyPointlessSuffering s ∧
    TheisticBeingExists s ∧ NoGratuitousSuffering s

end TruthCore.Comparison.RoweEvil
