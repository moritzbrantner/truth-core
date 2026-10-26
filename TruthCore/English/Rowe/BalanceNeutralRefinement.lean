import TruthCore.English.Rowe.EvidentialEvil

namespace TruthCore.English.Rowe

/-- Rowe p.336 n.3's proposed refinement: losing this good while preventing
suffering would leave the good/evil balance unchanged. This comparative relation
is an additional open interpretation, not inferred from a good's existence.
Reinterpreting the good-cost slot preserves the earlier structured inference;
no claim of equivalence with the published simplified premises is made. -/
def withBalanceNeutral (s : Sig)
    (BalanceNeutralGoodLoss : s.Outcome → s.Event → Prop) : Sig :=
  { s with GreaterGood := fun o e => s.GreaterGood o e ∨ BalanceNeutralGoodLoss o e }

/-- Stronger factual premise: the event also has no unavoidable balance-neutral
loss. Rowe's inductive support for this refinement is not proved here. -/
def RefinedGratuitousSufferingReading (s : Sig)
    (BalanceNeutralGoodLoss : s.Outcome → s.Event → Prop) : Prop :=
  GratuitousSufferingReading (withBalanceNeutral s BalanceNeutralGoodLoss)

/-- Weaker necessary constraint suggested by p.336 n.3: a balance-neutral good
loss may also block an obligation to prevent. It is still not a sufficient
license, and no actual permission or balancing calculation is established. -/
def RefinedPermissionConstraintReading (s : Sig)
    (BalanceNeutralGoodLoss : s.Outcome → s.Event → Prop) : Prop :=
  PermissionConstraintReading (withBalanceNeutral s BalanceNeutralGoodLoss)

end TruthCore.English.Rowe
