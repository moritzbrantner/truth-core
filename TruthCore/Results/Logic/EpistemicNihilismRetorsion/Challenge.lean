import TruthCore.Logic.EpistemicReasons
namespace TruthCore.Results.Logic.EpistemicNihilismRetorsion
open TruthCore.Logic.EpistemicReasons

/-- The retorsion (#1007): under global epistemic nihilism, no one has an
epistemic reason to believe it. It does not show that nihilism is false
(`nihilismConsistentAndUnbelievable`). -/
theorem nihilismSelfUndermining {Agent Content : Type}
    (Reason : Agent → Content → Prop) (nihilism : Content) :
    NihilismSelfUndermining Reason nihilism := by
  sorry

/-- Whoever has an epistemic reason to believe nihilism thereby has a reason,
so nihilism fails: the belief, if reasoned, refutes its own content. -/
theorem reasonedBeliefRefutesNihilism {Agent Content : Type}
    (Reason : Agent → Content → Prop) (Holds : Content → Prop) (nihilism : Content)
    (hExpresses : ExpressesNihilism Reason Holds nihilism) (a : Agent)
    (hReason : Reason a nihilism) : ¬ Holds nihilism := by
  sorry

/-- The gap, certified: an interpretation with one agent and no reasons, in
which nihilism holds and is believed with reason by no one. Self-undermining
is not falsity. -/
theorem nihilismConsistentAndUnbelievable : NihilismConsistentAndUnbelievable := by
  sorry
end TruthCore.Results.Logic.EpistemicNihilismRetorsion
