import TruthCore.Greek.Aristotle.Physics.Typed.Motion

/-! A consequence of the existing local act/potency commitments, not a new
source reading. The respect labels on two consecutive mover edges must differ.
This is a constraint on the encoded chain, not a temporal change of respect,
not a ban on all chains, and not a proof of the regress premise. -/
namespace TruthCore.Alternatives.RespectSwitch

/-- Whenever z moves y in r and y moves x in s, r and s are distinct. This
leaves alternating chains and cycles open; it asserts no global ordering of
the respect labels and no finite bound on chain length. -/
def ConsecutiveMoversHaveDistinctRespects {Being Respect : Type}
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ z y x r s, MovesIn z y r → MovesIn y x s → r ≠ s

end TruthCore.Alternatives.RespectSwitch
