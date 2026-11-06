module

public import TruthCore.Metaethics.GoodnessFormEnd

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessPropertyIdentity
open TruthCore.Metaethics.GoodnessFormEnd

theorem entailsDueActuality (f : Frame) (p : PropertyPresentation f)
    (h : PropertyIdentity p) : DueActualityThesis f := by
  change p.good = p.dueActual at h
  intro x r
  calc
    f.GoodIn x r ↔ p.denotes p.good x r := (p.goodMeaning x r).symm
    _ ↔ p.denotes p.dueActual x r := by rw [h]
    _ ↔ DueActuality f x r := p.dueMeaning x r

end TruthCore.Results.Metaethics.GoodnessPropertyIdentity
