# Factivity and coverage of the arrangement-selection rival

The existing `AcceptsUnselected` rival requires an accepted candidate that is
true at the designated arrangement and also at an explicitly distinct one. It
genuinely contradicts `CompleteRequiresSelection`. But it is not the exact
complement on a generic acceptance judgment: accepting a false candidate also
violates the selection requirement, without supplying a truthful nonselector.
The existing `TruthfulRival.checks` theorem already has a false-only control
and a positive truthful-rival construction. This batch reuses that theorem;
the missing work is first-class factivity and coverage, not a new permutation
or countermodel machinery.

`AcceptedAreTrue` is the independent OPEN policy `∀ p, adequate p → p a` for the
same mathematical Arrangement, selected `a` and supplied acceptance judgment.
It says nothing about warrant, causal production, real-world truth or actual
explanatory adequacy. Generic judgments can be mistaken. `AcceptedFalse` gives
an actual accepted-false countertuple rather than an untestable possible Other.
Exact matching-scope negatives for factivity and the old selection requirement
are separate propositions.

## Consequences and forks

Seven result configurations expose the following graph:

- The original selection requirement implies factivity by a sole-premise
  strength registration. Factivity alone does not select an arrangement.
- An accepted false candidate defeats factivity and independently defeats the
  old selection requirement. It need not witness the old truthful rival.
- The old truthful rival defeats the SAME exact selection requirement by
  composing the unchanged `TruthfulRival.checks` theorem.
- Explicit excluded middle gives complete selection OR accepted truthful
  nonselection OR accepted false candidate. This is coverage, not exclusivity:
  a judgment may accept both false and truthful nonselecting candidates.
- With factivity explicitly supplied, the last case is excluded and the usual
  selection OR truthful-nonselection fork follows. That coverage policy is not
  hidden in the old independent `adequate` predicate.

The full old truthful rival stays an alternative. The exact negative is added
beside it, so refuting a truthful nonselector alone cannot eliminate the false-
acceptance case on a generic judgment. No finite roster of philosophical schools
is declared exhaustive. An account defining adequate explanations as factive
may supply that policy, but this proof does not establish it for every judgment
or independently certify any actual explanation.

## Exact exported controls

For every designated arrangement in the ORIGINAL arena, the certificate exports:

1. `falseOnly`: acceptance means falsity at that arrangement. It accepts a
   specific false candidate, fails selection and has no truthful nonselection
   rival. This models an inadmissible or mistaken generic judgment, not a
   theory that false propositions are genuinely adequate explanations.
2. `trueOnly`: acceptance means truth there. It is factive but supplies a
   truthful nonselecting candidate, so selection fails. The existing theorem's
   swapped-label construction supplies the distinct arrangement; no new
   mathematical substitute is introduced. Arbitrary truth is not thereby
   established explanatory adequacy.
3. `selectsOnly`: acceptance is deliberately selection-defined. Selection and
   factivity hold and an equality-selector is explicitly accepted, so this
   calibration is nonempty. The positive selection property is analytic in
   this control and supplies no independent explanatory warrant.

The last two controls witness strictness of the selection-to-factivity order
and retain a positive calibration without choosing a true metaphysical theory.
No original model value or frozen Challenge is changed. The five direct logical
results are zero-axiom; the two compositions using the old Mathlib arrangement
control retain its approved `propext`, `Classical.choice`, `Quot.sound` policy.
Strength/projection, coverage and composition labels do not advertise independent
philosophical closure.

Reuse started with related/dossiers for both original propositions, then their
exact definitions and the complete original truthful-rival proof. Source
attribution stays deferred and no existing claim changes. Findings and rejected
inferences are persisted in the existing ordering-cardinality attempt. Actual
root-premise effects come from `frontier-diff` in the PR; adding a conditional
fork is not a premise discharge or a whole-repository audit completion.
