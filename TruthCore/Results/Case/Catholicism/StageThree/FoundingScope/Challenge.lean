import TruthCore.Case.Catholicism.StageThree.FoundingScope

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope

/-- The scope premise `STMT-MANDATE-COVERS-JESUS-FOUNDING-WITH-TEACHING` follows
from its instance at the Catholic Church and stage 6: if every visible
authoritative society Jesus founded is the Catholic Church, and Jesus founded
the Catholic Church in the exercise of any mandate he holds, commissioning it
to teach, then he so founded every such society. -/
theorem mandate_scope_from_catholic_church_founding (σ : Signature) (A : Agency σ)
    (hNarrow : MandatedFoundingOfCatholicChurch σ A)
    (hIdentity : ChristsChurchIsCatholicChurch σ) :
    MandatedFoundingWithTeaching σ A := by
  sorry

end TruthCore.Results.Case.Catholicism.StageThree.FoundingScope
