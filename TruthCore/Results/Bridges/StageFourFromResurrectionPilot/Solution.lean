import TruthCore.History.Resurrection
namespace TruthCore.Results.Bridges.StageFourFromResurrectionPilot
open TruthCore.Case.Catholicism
open TruthCore.History.Resurrection
/-- Bridge (#401), a definitional decomposition, not a derivation: the resurrection pilot's
two central answer cells, that Jesus claimed divine authority
(`STMT-PILOT-JESUS-CLAIMS`) and that he rose (`STMT-PILOT-ROSE`), are stage 4 of
the case (`STMT-JESUS-CLAIMED-DIVINE-AUTHORITY-AND-ROSE`) for the pilot state's
core signature. The pilot reuses the case's `Signature` (`State.core`), so the
proof is conjunction introduction on the same predicates. Stage 4 thereby
rests on the two pilot cells, as `Root.lean` intends for its historical
findings; it does not establish either cell, which remain open
(`docs/resurrection-pilot.md`). -/
theorem jesusClaimedDivineAuthorityAndRoseOfPilot (s : State) (hClaims : JesusClaims s) (hRose : Rose s) :
    JesusClaimedDivineAuthorityAndRose s.core :=
  ⟨hClaims, hRose⟩
end TruthCore.Results.Bridges.StageFourFromResurrectionPilot
