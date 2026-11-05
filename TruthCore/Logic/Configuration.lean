module

/-! Reusable contradiction target for explicitly parameterized configuration proofs. -/

@[expose] public section

namespace TruthCore.Logic
/-- Logical falsity only, with no philosophical interpretation or hidden premises. -/
def ConfigurationFalse : Prop := False
end TruthCore.Logic
