namespace TruthCore.Causality.NecessaryBeingSurvey

/-- An uninterpreted predicate: `causableAtLeast n` represents the source's
claim that it is possible to cause a situation with at least `n` contingent
things. This abstraction does not supply a modal frame, a causal relation,
or monotonicity in `n`; those would be substantive additional commitments. -/
def FiveCausable (causableAtLeast : Nat → Prop) : Prop :=
  causableAtLeast 5

/-- A7c step 2's reported transfer premise, specialized to contingent things.
It must be assumed explicitly, not derived from what "at least" means:
causing distinct situations may require distinct causal conditions. -/
def CountDescent (causableAtLeast : Nat → Prop) : Prop :=
  ∀ n : Nat, 1 < n → causableAtLeast n → causableAtLeast (n - 1)

/-- The narrow A7c step 3 conclusion: a cause of the situation with at least
one contingent thing is possible. No noncontingent cause follows yet. -/
def OneCausable (causableAtLeast : Nat → Prop) : Prop :=
  causableAtLeast 1

end TruthCore.Causality.NecessaryBeingSurvey
