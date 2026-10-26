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
  intro x g hGod hIn
  -- INF-ARIST-MET-998B-BEING-NOT-A-GENUS: being is not a genus (Aristotle),
  have hNotGenus : BeingIsNotAGenusReading IsGenus ens :=
    TruthCore.Results.Aristotle.Metaphysics.BeingNotAGenus.beingNotAGenus
      IsGenus DifferentiaOf SaidOf ens hHas hBeings hNotSaid
  -- INF-AQUINAS-ST-I-Q3-A5-GOD-IN-NO-GENUS: the genus God would be in is a genus,
  have hGenus : IsGenus g := hUnder x g hIn
  -- and it would be being,
  have hEq : g = ens := hWouldBe x g hGod hIn
  -- so being would be a genus.
  exact hNotGenus (hEq ▸ hGenus)

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
  intro h
  -- Terms are `Bool`: `false` is being, `true` the one genus, whose differentia
  -- is `false`; only being is said of anything. God is in the genus `true`.
  exact h Unit Bool (fun t => t = true) (fun d g => d = false ∧ g = true)
    (fun t _ => t = false) false (fun _ => True) (fun _ g => g = true)
    (fun g hg => ⟨false, rfl, hg⟩)
    (fun _ _ _ _ => rfl)
    (fun g _ hg _ hs => Bool.noConfusion (hg.symm.trans hs))
    (fun _ _ hin => hin)
    () true trivial rfl

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
  intro h
  exact h Unit Unit (fun _ => False) (fun _ _ => False) (fun _ _ => False) ()
    (fun _ => True) (fun _ _ => True)
    (fun _ hg => hg.elim) (fun _ _ hg _ => hg.elim) (fun _ _ hg _ _ => hg.elim)
    (fun _ _ _ _ => rfl)
    () () trivial trivial
end TruthCore.Results.Aquinas.SummaTheologiae.GodInNoGenus
