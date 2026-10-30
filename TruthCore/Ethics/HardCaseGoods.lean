import TruthCore.Ethics.HardCaseTyped

/-! A supplementary thin-profile test for #699. The goods and their damage
are stipulated separately from moral verdicts; they are not source readings,
real-world facts, or a claim that any richer theory admits both verdicts. -/
namespace TruthCore.Ethics.HardCaseGoods
open TruthCore.Ethics.HardCaseTyped

inductive HumanGood | life | bodilyIntegrity deriving DecidableEq

/-- A single positive classification and a single damage assignment are shared
by both verdicts. `good` says a person's life or bodily integrity is a good in
a context; `damages` states that the specified action damages it. The example
supplies these relations and does not derive their truth or normative weight. -/
def GoodsOmission : Prop :=
  ∃ (f : Facts) (good : Context → Person → HumanGood → Prop)
    (damages : Context → Act → Person → HumanGood → Prop) (yes no : Verdict),
    HardCases f ∧
    good .violation .victim .bodilyIntegrity ∧
    good .killing .victim .life ∧
    ¬ good .conflict .offender .life ∧
    damages .violation .violate .victim .bodilyIntegrity ∧
    damages .killing .kill .victim .life ∧
    ¬ damages .violation .violate .victim .life ∧
    yes.forbidden .violation .violate ∧ yes.forbidden .killing .kill ∧
    ¬ no.forbidden .violation .violate ∧ ¬ no.forbidden .killing .kill
end TruthCore.Ethics.HardCaseGoods
