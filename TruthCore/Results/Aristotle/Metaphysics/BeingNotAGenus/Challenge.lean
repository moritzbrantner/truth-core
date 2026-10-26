import TruthCore.Greek.Aristotle.MetaphysicsIII3
namespace TruthCore.Results.Aristotle.Metaphysics.BeingNotAGenus
open TruthCore.Greek.Aristotle.Metaphysics

/-- *Metaphysics* III.3, 998b22-27: every genus has a differentia; being is said
of every differentia; a genus is not said of its own differentiae. So being is
not a genus: if it were, it would have a differentia, being would be said of
that differentia, and the genus being would be said of its own differentia.

The term `ens` is arbitrary: the same proof shows that *one*, or any term said
of every differentia of every genus, is not a genus. -/
theorem beingNotAGenus {Term : Type}
    (IsGenus : Term → Prop) (DifferentiaOf SaidOf : Term → Term → Prop)
    (ens : Term)
    (hHas : EveryGenusHasADifferentiaReading IsGenus DifferentiaOf)
    (hBeings : DifferentiaeAreBeingsReading IsGenus DifferentiaOf SaidOf ens)
    (hNotSaid : GenusNotSaidOfOwnDifferentiaeReading IsGenus DifferentiaOf SaidOf) :
    BeingIsNotAGenusReading IsGenus ens := by
  sorry

/-- Omission test: without "every genus has a differentia", a genus with no
differentiae satisfies the other two premises and being is a genus. -/
theorem needsEveryGenusHasADifferentia :
    ¬ ∀ (Term : Type) (IsGenus : Term → Prop)
      (DifferentiaOf SaidOf : Term → Term → Prop) (ens : Term),
      DifferentiaeAreBeingsReading IsGenus DifferentiaOf SaidOf ens →
      GenusNotSaidOfOwnDifferentiaeReading IsGenus DifferentiaOf SaidOf →
      BeingIsNotAGenusReading IsGenus ens := by
  sorry

/-- Omission test: without "every differentia is a being", a genus whose
differentia being is not said of satisfies the other two premises. -/
theorem needsDifferentiaeAreBeings :
    ¬ ∀ (Term : Type) (IsGenus : Term → Prop)
      (DifferentiaOf SaidOf : Term → Term → Prop) (ens : Term),
      EveryGenusHasADifferentiaReading IsGenus DifferentiaOf →
      GenusNotSaidOfOwnDifferentiaeReading IsGenus DifferentiaOf SaidOf →
      BeingIsNotAGenusReading IsGenus ens := by
  sorry

/-- Omission test: without "a genus is not said of its own differentiae", a
genus said of its differentia satisfies the other two premises. -/
theorem needsGenusNotSaidOfOwnDifferentiae :
    ¬ ∀ (Term : Type) (IsGenus : Term → Prop)
      (DifferentiaOf SaidOf : Term → Term → Prop) (ens : Term),
      EveryGenusHasADifferentiaReading IsGenus DifferentiaOf →
      DifferentiaeAreBeingsReading IsGenus DifferentiaOf SaidOf ens →
      BeingIsNotAGenusReading IsGenus ens := by
  sorry
end TruthCore.Results.Aristotle.Metaphysics.BeingNotAGenus
