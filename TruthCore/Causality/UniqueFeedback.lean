namespace TruthCore.Causality.UniqueFeedback

/-- Issue #311 analyst-defined state equations, not a causal or grounding
relation. The first gate negates the second bit; the second conjoins both
bits. No observed boundary value or temporal evolution is supplied. -/
def Consistent (state : Bool × Bool) : Prop :=
  state.1 = !state.2 ∧ state.2 = (state.1 && state.2)

/-- The gates genuinely vary with their inputs: negation distinguishes the
two bits, and conjunction depends on each input when the other is true.
This is truth-table sensitivity, not actual causal power or intervention. -/
def Sensitive : Prop :=
  (!false : Bool) ≠ !true ∧
  (false && true : Bool) ≠ (true && true) ∧
  (true && false : Bool) ≠ (true && true)

/-- A nonempty and uniquely determined feedback solution with sensitive
local gates. The explicit witness prevents vacuous uniqueness. Neither
ontological existence nor sufficient explanation is a predicate here;
uniqueness therefore establishes neither explanatory adequacy nor its
failure. The feedback is logical, not an asserted cyclic causal history. -/
def Controls : Prop :=
  Sensitive ∧ Consistent (true, false) ∧
    ∀ state, Consistent state → state = (true, false)

end TruthCore.Causality.UniqueFeedback
