module

public import TruthCore.Logic.EpistemicReasons

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicNihilismRetorsion
open TruthCore.Logic.EpistemicReasons

/-- The retorsion (#1007): under global epistemic nihilism, no one has an
epistemic reason to believe it. It does not show that nihilism is false
(`nihilismConsistentAndUnbelievable`). -/
theorem nihilismSelfUndermining {Agent Content : Type}
    (Reason : Agent → Content → Prop) (nihilism : Content) :
    NihilismSelfUndermining Reason nihilism := by
  intro hNihilism a
  -- Nihilism denies every reason, the reason to believe nihilism included.
  exact hNihilism a nihilism

/-- Whoever has an epistemic reason to believe nihilism thereby has a reason,
so nihilism fails: the belief, if reasoned, refutes its own content. -/
theorem reasonedBeliefRefutesNihilism {Agent Content : Type}
    (Reason : Agent → Content → Prop) (Holds : Content → Prop) (nihilism : Content)
    (hExpresses : ExpressesNihilism Reason Holds nihilism) (a : Agent)
    (hReason : Reason a nihilism) : ¬ Holds nihilism := by
  intro hHolds
  exact hExpresses.mp hHolds a nihilism hReason

/-- The gap, certified: an interpretation with one agent and no reasons, in
which nihilism holds and is believed with reason by no one. Self-undermining
is not falsity. -/
theorem nihilismConsistentAndUnbelievable : NihilismConsistentAndUnbelievable := by
  refine ⟨Unit, Unit, fun _ _ => False, fun _ => EpistemicNihilism (fun (_ : Unit) (_ : Unit) => False),
    (), Iff.rfl, fun _ _ h => h, fun _ h => h, ⟨()⟩⟩
end TruthCore.Results.Logic.EpistemicNihilismRetorsion
