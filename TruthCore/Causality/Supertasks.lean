namespace TruthCore.Causality

/-- An abstract order with stages indexed by the natural numbers and a separate
limit endpoint. This is an order model, not yet a physical clock or a claim
that infinitely many physical operations can occur in finite time. -/
inductive SupertaskMoment where
  | stage (index : Nat)
  | limit

/-- Every stage precedes the limit, although no stage is the final stage. -/
def SupertaskPrecedes : SupertaskMoment → SupertaskMoment → Prop
  | .stage n, .stage m => n < m
  | .stage _, .limit => True
  | .limit, _ => False

/-- A Boolean output has a terminal value under the explicitly chosen
*eventual stability* criterion. Numerical sequence convergence is a distinct
notion; this strong discrete criterion is not imposed on real-valued series. -/
def StableAtLimit (output : Nat → Bool) (terminal : Bool) : Prop :=
  ∃ cutoff, ∀ n, cutoff ≤ n → output n = terminal

/-- The abstract schedule has no last stage but has a distinguished endpoint,
and at least one output assignment is coherent there. This is not a claim that
all schedules have a coherent terminal output. -/
def EndlessStagesWithStableEndpoint : Prop :=
  (∀ n, SupertaskPrecedes (.stage n) .limit) ∧
    (∀ n, ∃ m, SupertaskPrecedes (.stage n) (.stage m)) ∧
      ∃ output : Nat → Bool, ∃ terminal : Bool, StableAtLimit output terminal

/-- The idealized Thomson-lamp-style output toggles after every stage. -/
def AlternatingStageOutput : Nat → Bool
  | 0 => false
  | n + 1 => !AlternatingStageOutput n

/-- Under the stipulated stability criterion, the alternating output has no
limit state. This does not by itself prove physical impossibility. -/
def AlternatingOutputHasNoStableLimit : Prop :=
  ∀ terminal : Bool, ¬ StableAtLimit AlternatingStageOutput terminal

/-- The sum of `n` stages, each costing one discrete time unit. This is the
partial-sum sequence for the divergent series 1 + 1 + 1 + ... . -/
def UnitCostPartialSum : Nat → Nat
  | 0 => 0
  | n + 1 => UnitCostPartialSum n + 1

/-- No finite unit-cost budget bounds every partial sum. The result depends
on the fixed positive stage cost, not on infinity alone. -/
def UnitCostSeriesUnbounded : Prop :=
  ∀ budget : Nat, ∃ n, budget < UnitCostPartialSum n

/-- A finite-capacity world can accommodate a particular finite task prefix.
The capacity is the world's natural-number upper bound, not a claim about
physically or metaphysically possible worlds. -/
def PrefixFitsFiniteWorld (capacity segmentLength : Nat) : Prop :=
  segmentLength ≤ capacity

/-- Every finite prefix fits *some* finite world, but no one such world fits
all prefixes. This models the invalid shift from `∀ n, ◇ P n` to
`◇ ∀ n, P n` without claiming anything about the actual modal accessibility
relation of physical worlds. -/
def FinitePrefixesFitSeparatelyNotUniformly : Prop :=
  (∀ segmentLength : Nat, ∃ capacity : Nat,
    PrefixFitsFiniteWorld capacity segmentLength) ∧
    ¬ (∃ capacity : Nat, ∀ segmentLength : Nat,
      PrefixFitsFiniteWorld capacity segmentLength)

/-- A simplified Ross–Littlewood-style urn: at finite stage `n`, the balls
present are precisely those numbered strictly above `n` and at most `2*n`.
It models insertion of two new balls and removal of one at each positive
stage, rather than Littlewood's historical ten-to-one version. -/
def UrnResident (stage ball : Nat) : Prop :=
  stage < ball ∧ ball ≤ stage + stage

/-- Each fixed ball eventually disappears, arbitrarily long blocks of
distinct balls occur at finite stages, and there is no uniform stage after
which every urn is empty. Pointwise and uniform eventual absence differ.
The result does *not* assert any physical urn can perform infinitely many
operations, or that a finite-stage cardinality has a finite limit. -/
def UrnPointwiseAbsenceNotUniformEmptiness : Prop :=
  (∀ ball : Nat, ∃ cutoff : Nat,
    ∀ stage : Nat, cutoff ≤ stage → ¬ UrnResident stage ball) ∧
  (∀ count : Nat, ∃ stage : Nat,
    ∀ offset : Nat, offset < count →
      UrnResident stage (stage + offset + 1)) ∧
  ¬ (∃ cutoff : Nat, ∀ stage : Nat,
    cutoff ≤ stage → ∀ ball : Nat, ¬ UrnResident stage ball)

/-- An observation restricted to stages at or before an arbitrary finite
cutoff does not distinguish an eventually-false output from an eventually-
true output. Knowing the full generating rule is stronger information than
observing a finite prefix, so this is an epistemic countermodel only. -/
def FiniteObservationCannotFixAllStableOutputs : Prop :=
  ∀ cutoff : Nat,
    ∃ first second : Nat → Bool,
      (∀ n : Nat, n ≤ cutoff → first n = second n) ∧
      StableAtLimit first false ∧ StableAtLimit second true

end TruthCore.Causality
