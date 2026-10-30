import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question105.Article5
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsMaximeEns IsFirstUnmovedMover
  MaximeEnsIsGod)

/-- Separate sufficient equality-decision interface. All nonlogical premises remain open.
No existence follows from naming or identifying supplied witnesses. No necessity,
minimality, strict-strength or philosophical-discharge claim. The historical
end, where present, retains the existing structural transcription. -/
theorem firstMoverIsMaximeEns {Being : Type} {Respect : Type}
    [DecidableEq Being]
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (God : Being → Prop)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hGod : MaximeEnsIsGod InAct MoreIn esse God)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God) :
    FirstUnmovedMoverIsMaximeEns MovedIn MovesIn InAct MoreIn esse := by
  intro f hF m hMax
  obtain ⟨⟨x, r, hMoves⟩, hUnmoved⟩ := hF
  -- INF-AQUINAS-FIRST-MOVER-IS-MAXIME-ENS: the genus principle at esse for m
  have hCauses : CausesAllInGenus InAct CausesIn esse m := hGenus esse m hMax
  -- f is not other than m
  have hNotOther : ¬ f ≠ m := by
    intro hNe
    have hEsse : InAct f esse := hBeing f r (hInAct f x r hMoves)
    obtain ⟨r', hMoved⟩ :=
      hApplied m f (hGod m hMax) hNe (hCauses f hNe hEsse) ⟨x, r, hMoves⟩
    exact hUnmoved r' hMoved
  by_cases hSame : f = m
  · exact hSame
  · exact (hNotOther hSame).elim

end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity
