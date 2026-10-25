import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-!
A consequence of existing fourth-way vocabulary, not a new reading equating
causation with sustaining dependence, withdrawal power, or arbitrary modal power.
The argument uses the existing causal-comparison premise from Metaphysics II.1.
ST I q.9 a.2 motivates investigating sustaining dependence, but the mapping from
that distinct notion to `CausesIn` at `esse` remains open.
-/
namespace TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A maximum in being has no distinct cause of its being in the existing
`CausesIn` relation. This does not exclude self-causation or arbitrary powers. -/
def MaximumHasNoDistinctEsseCause {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn esse m → ∀ c, c ≠ m → ¬ CausesIn c m esse

/-- The existing fourth-way witness also has no distinct `CausesIn` cause at
`esse`. The witness is the same maximum and cause of all other beings. -/
def MaximalCauseWithNoDistinctEsseCause {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∃ m, IsMaximumIn InAct MoreIn esse m ∧
    CausesAllInGenus InAct CausesIn esse m ∧
    ∀ c, c ≠ m → ¬ CausesIn c m esse

end TruthCore.Case.Catholicism
