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

end TruthCore.Causality
