import TruthCore.Comparison.ProblemOfEvil
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
namespace TruthCore.Results.Comparison.ProblemOfEvil.ObjectionOneDeniedByCatholic
open TruthCore.Comparison.ProblemOfEvil
theorem catholicDeniesObjectionOne (s : Sig) (hCatholic : Catholic s) : ObjectionOneFails s := by
  intro hObjection
  obtain ⟨_, hPrivation, _, ⟨x, p, hDue, hLacks⟩, hSense, hPotency, hAct, hReduction,
    hNotBoth, hPerSe, hRegress, hIdentification, _⟩ := hCatholic
  -- INF-CATHOLIC-EVIL-EXISTS: a due good is lacking (q.48 a.2), and that lack is evil (q.48 a.3).
  have hEvil : ∃ x, s.Evil x := ⟨x, (hPrivation x).mpr ⟨p, hDue, hLacks⟩⟩
  -- The prima via (#151): a first mover moved by none cannot be lacking.
  have hFirst := TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.primaVia
    s.motion.MovedIn s.motion.MovesIn s.motion.InPotency s.motion.InAct s.motion.MovesAsMoved
    hSense hPotency hAct hReduction hNotBoth hPerSe hRegress
  -- INF-CATHOLIC-DENIES-OBJECTION-ONE: that mover is God, and by the objection's
  -- conditional God excludes the evil there is.
  exact hFirst fun ⟨g, hMover⟩ => hObjection g (hIdentification g hMover) hEvil
end TruthCore.Results.Comparison.ProblemOfEvil.ObjectionOneDeniedByCatholic
