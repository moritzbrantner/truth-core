module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPotencyTheory
public import TruthCore.Logic.CaseNonContradiction
public import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.DefinitionalAnalysesConservative.Solution

/-!
# The adopted sense of potency (owner decision, #1007)

The generic vocabulary keeps `InPotency` independent for comparing rival senses.
In the adopted configuration, potency to a respect is capacity for that respect
without actually having it. This is a definition, not a thesis about an arbitrary
independent potency predicate. `CanBe` and `InAct` remain unconstrained; in
particular this definition does not establish that something has a capacity.

The owner decision adopts the interpretation. The existing conservative-analysis
result certifies the exact logical boundary: such an analysis implies generic
non-overlap, and generic non-overlap permits some capacity analysis. It does not
refute a rival sense that permits a power to persist while it is exercised.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency

/-- Adopted potency: x can be F in respect r and is not actually F in that
same respect. Capacity is distinct from potency: a currently exercised capacity
need not be an unactualized capacity. -/
def InPotency {Being : Sort u} {Respect : Sort v}
    (InAct CanBe : Being → Respect → Prop) (x : Being) (r : Respect) : Prop :=
  CanBe x r ∧ ¬ InAct x r

/-- F7 in the adopted sense, with exactly the same act predicate and respect
on each side. This says nothing about independently supplied potency relations. -/
def NonOverlap {Being : Sort u} {Respect : Sort v}
    (InAct CanBe : Being → Respect → Prop) : Prop :=
  NotActAndPotencyInSameRespectReading InAct (InPotency InAct CanBe)

/-- The IX.6-shaped analysis is true by definition in the adopted configuration;
it is not proved for a separately supplied potency predicate. -/
theorem analysis {Being Respect : Type} (InAct CanBe : Being → Respect → Prop) :
    TruthCore.Greek.Aristotle.Metaphysics.PotencyIsUnactualizedCapacityReading
      InAct (InPotency InAct CanBe) CanBe := by
  intro x r
  exact Iff.rfl

/-- F1 excludes simultaneous act and adopted potency in the same respect.
No excluded middle, capacity-existence, causal or modal premise is used. -/
theorem nonOverlap {Being Respect : Type} (InAct CanBe : Being → Respect → Prop)
    (hF1 : TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction.{1, 1}) :
    NonOverlap InAct CanBe := by
  intro x r h
  exact hF1 Being Respect InAct x r ⟨h.1, h.2.2⟩

/-- Compose the existing conservative-analysis certificate at the adopted
predicate. Lean's internal non-contradiction is built into this imported proof;
`nonOverlap` separately retains the explicit F1 interface for the case. -/
theorem nonOverlapByConservativeAnalysis {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop) : NonOverlap InAct CanBe := by
  exact TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.DefinitionalAnalysesConservative.definitionalAnalysesConservative.1
    Being Respect InAct (InPotency InAct CanBe) CanBe (analysis InAct CanBe)

end TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency
