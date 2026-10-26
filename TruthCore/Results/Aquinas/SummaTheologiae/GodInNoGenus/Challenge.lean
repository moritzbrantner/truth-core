import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article5
import TruthCore.Results.Aristotle.Metaphysics.BeingNotAGenus.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.GodInNoGenus
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics

/-- ST I q.3 a.5 co., second proof: if God were in a genus, that genus would
be being; but being is not a genus (Aristotle, *Metaphysics* III.3, which
Aquinas cites and restates: every genus has differentiae outside its essence,
and no differentia is outside being). So God is in no genus.

Being-not-a-genus is not a premise here: it is derived by Aristotle's
argument (`BeingNotAGenus.beingNotAGenus`) from its three premises. -/
theorem godInNoGenus {Being Term : Type}
    (IsGenus : Term → Prop) (DifferentiaOf SaidOf : Term → Term → Prop)
    (ens : Term) (IsGod : Being → Prop) (InGenus : Being → Term → Prop)
    (hHas : EveryGenusHasADifferentiaReading IsGenus DifferentiaOf)
    (hBeings : DifferentiaeAreBeingsReading IsGenus DifferentiaOf SaidOf ens)
    (hNotSaid : GenusNotSaidOfOwnDifferentiaeReading IsGenus DifferentiaOf SaidOf)
    (hUnder : InGenusOnlyUnderAGenusReading IsGenus InGenus)
    (hWouldBe : GenusOfGodWouldBeBeingReading IsGod InGenus ens) :
    GodIsInNoGenusReading IsGod InGenus := by
  sorry

/-- Omission test: the conditional "God's genus would be being" is needed. A
God in a genus other than being satisfies all four other premises. -/
theorem needsGenusOfGodWouldBeBeing :
    ¬ ∀ (Being Term : Type) (IsGenus : Term → Prop)
      (DifferentiaOf SaidOf : Term → Term → Prop) (ens : Term)
      (IsGod : Being → Prop) (InGenus : Being → Term → Prop),
      EveryGenusHasADifferentiaReading IsGenus DifferentiaOf →
      DifferentiaeAreBeingsReading IsGenus DifferentiaOf SaidOf ens →
      GenusNotSaidOfOwnDifferentiaeReading IsGenus DifferentiaOf SaidOf →
      InGenusOnlyUnderAGenusReading IsGenus InGenus →
      GodIsInNoGenusReading IsGod InGenus := by
  sorry

/-- Omission test: "what is in a genus is under a genus" is needed. A God
"in" being, where being is no genus, satisfies the other premises. -/
theorem needsInGenusOnlyUnderAGenus :
    ¬ ∀ (Being Term : Type) (IsGenus : Term → Prop)
      (DifferentiaOf SaidOf : Term → Term → Prop) (ens : Term)
      (IsGod : Being → Prop) (InGenus : Being → Term → Prop),
      EveryGenusHasADifferentiaReading IsGenus DifferentiaOf →
      DifferentiaeAreBeingsReading IsGenus DifferentiaOf SaidOf ens →
      GenusNotSaidOfOwnDifferentiaeReading IsGenus DifferentiaOf SaidOf →
      GenusOfGodWouldBeBeingReading IsGod InGenus ens →
      GodIsInNoGenusReading IsGod InGenus := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.GodInNoGenus
