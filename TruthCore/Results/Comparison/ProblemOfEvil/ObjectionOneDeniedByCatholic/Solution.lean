import TruthCore.Comparison.ProblemOfEvil
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
namespace TruthCore.Results.Comparison.ProblemOfEvil.ObjectionOneDeniedByCatholic
open TruthCore.Comparison.ProblemOfEvil
theorem catholicDeniesObjectionOne : ∀ s, Catholic s → ObjectionOneConditional s → False := by
  intro s hCatholic hObjection
  obtain ⟨⟨_, hPrivation, _⟩, ⟨x, p, hDue, hLacks⟩, ⟨hSense, hPotency, hAct, hReduction,
    hNotBoth, hPerSe, hRegress⟩, hIdentification, _⟩ := hCatholic
  -- INF-CATHOLIC-EVIL-EXISTS: a due good is lacking (q.48 a.2), and that lack is evil (q.48 a.3).
  have hEvil : ∃ x, s.Evil x := ⟨x, (hPrivation x).mpr ⟨p, hDue, hLacks⟩⟩
  -- INF-CATHOLIC-GOD-CANNOT-BE-LACKING: the prima via (#151) makes a first mover moved by
  -- none impossible to lack, and what all understand as God is that mover.
  have hFirst := TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.primaVia
    s.motion.MovedIn s.motion.MovesIn s.motion.InPotency s.motion.InAct s.motion.MovesAsMoved
    hSense hPotency hAct hReduction hNotBoth hPerSe hRegress
  -- INF-CATHOLIC-DENIES-OBJECTION-ONE: any such God would, by the objection, exclude the evil.
  exact hFirst fun ⟨g, hMover⟩ => hObjection g (hIdentification g hMover) hEvil
end TruthCore.Results.Comparison.ProblemOfEvil.ObjectionOneDeniedByCatholic
