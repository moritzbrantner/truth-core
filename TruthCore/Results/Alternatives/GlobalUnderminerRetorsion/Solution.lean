import TruthCore.Alternatives.FirstClosure
import TruthCore.Alternatives.Retorsion
import TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial.Solution
import TruthCore.Results.Logic.PerformedDenial.StaticControl.Solution

namespace TruthCore.Results.Alternatives.GlobalUnderminerRetorsion
open TruthCore.Logic.PerformedDenial
open TruthCore.Alternatives.Retorsion
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.McTaggart

/-- The Eleatic retorsion (*Physics* VIII.3, 254a27-30) as an instance of the
performed-denial schema, with the presupposition link as its hypothesis. -/
theorem eleaticRetorsionInstance : EleaticRetorsionInstance := by
  intro _ _ MovedIn Opines asOpinion hLink hHeld hNothing
  obtain ⟨x, hx⟩ := hHeld
  -- The link makes the opining an occurring Eleatic episode, and that episode
  -- is an accurate performed denial of every Eleatic episode, against #516.
  exact TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial.noAccurateDenial
    (eleaticOccurs MovedIn) (eleaticDenies MovedIn Opines asOpinion)
    ⟨opinionToken asOpinion x (NothingIsMovedReading MovedIn), hLink x _ hx, ⟨x, rfl, hx⟩,
      nothingIsMoved_noEpisodeOccurs hNothing⟩

/-- McTaggart's § 511 answer escapes the schema at the presupposition link. -/
theorem mcTaggartEscapesRetorsion : McTaggartEscapesRetorsion := by
  refine ⟨?_, ?_, ?_, TruthCore.Results.Logic.PerformedDenial.StaticControl.staticControl⟩
  · intro _ _ _ hReply hLink
    obtain ⟨⟨x, p, hx⟩, hNo⟩ := hReply
    exact hNo x p hx (hLink x p hx)
  · intro _ _ _ _ _ asOpinion hReply hBridge hLink
    exact appearingsDoNotChange_denies_opinionIsMotion (asOpinion := asOpinion) hReply hBridge hLink
  · obtain ⟨hHeld, hBridge, hNoA, hAll, hNothing, -, -, -⟩ :=
      TruthCore.Alternatives.FirstClosure.opinionGate
    have hReply : AppearingsDoNotChangeReading (fun (_ : Unit) (_ : Prop) => True)
        (fun _ => False) := ⟨⟨(), True, trivial⟩, fun _ _ _ h => h⟩
    refine ⟨_, _, _, _, ⟨hNoA, hAll⟩, hReply, hBridge, hHeld, hNothing,
      ⟨(), trivial⟩, fun ⟨_, h⟩ => h, ?_, ?_⟩
    · intro hLink
      exact hReply.2 () True trivial (hLink () True trivial)
    · intro asOpinion hLink
      exact appearingsDoNotChange_denies_opinionIsMotion (asOpinion := asOpinion) hReply hBridge hLink

end TruthCore.Results.Alternatives.GlobalUnderminerRetorsion
