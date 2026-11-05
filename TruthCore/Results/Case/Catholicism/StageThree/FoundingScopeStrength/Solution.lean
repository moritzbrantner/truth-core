module

public import TruthCore.Case.Catholicism.StageThree.FoundingScope

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingScopeStrength
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
/-- The universal scope premise entails its instance at the Catholic Church:
if every visible authoritative society Jesus founded was founded in the
exercise of any mandate he holds and commissioned to teach, so was the
Catholic Church, should he have founded it as such a society. Registers
`STMT-MANDATE-COVERS-JESUS-FOUNDING-WITH-TEACHING` strengthens
`STMT-MANDATE-COVERS-JESUS-FOUNDING-OF-CATHOLIC-CHURCH` (#1017). -/
theorem mandateScopeStrongEntailsCatholicChurchScope (σ : Signature) (A : Agency σ)
    (hScope : MandatedFoundingWithTeaching σ A) : MandatedFoundingOfCatholicChurch σ A := by
  exact scope_implies_catholic_church_scope σ A hScope
end TruthCore.Results.Case.Catholicism.StageThree.FoundingScopeStrength
