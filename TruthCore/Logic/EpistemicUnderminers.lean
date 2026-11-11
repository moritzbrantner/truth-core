module

public import TruthCore.Logic.EpistemicReasons
public import TruthCore.Logic.ReflectiveCoherence

/-!
Scoped analyst readings of global epistemic underminers. A reason can favor
belief without warranting an actual belief. Benchmark accuracy, responsiveness
across states and semantic validity answer different questions. Requiring an
earlier demonstration certificate and requiring a prior known premise used by
that demonstration have different consequences for regress.
-/

@[expose] public section

namespace TruthCore.Logic.EpistemicUnderminers

open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.ReflectiveCoherence

/-- The exact negation of global epistemic nihilism in the thin F6 sense. -/
def EpistemicNihilismFails {Agent Claim : Type} (Reason : Agent → Claim → Prop) : Prop :=
  ¬ EpistemicNihilism Reason

/-- Some agent actually believes a content and meets the supplied warrant
standard for that belief. Warrant here need not entail truth. -/
def SomeJustifiedBelief {Agent Claim : Type} (Believes Warrant : Agent → Claim → Prop) : Prop :=
  ∃ a p, Believes a p ∧ Warrant a p

/-- No actual belief meets the supplied warrant standard. -/
def NoJustifiedBeliefs {Agent Claim : Type} (Believes Warrant : Agent → Claim → Prop) : Prop :=
  ¬ SomeJustifiedBelief Believes Warrant

/-- A reason and an actual belief are present in a case that meets the
independently supplied basing, adequacy and undefeatedness conditions. -/
def SomeEligibleReasonUptake {Agent Claim : Type}
    (Reason Believes Eligible : Agent → Claim → Prop) : Prop :=
  ∃ a p, Reason a p ∧ Believes a p ∧ Eligible a p

/-- The adequacy bridge: eligible uptake of a reason meets the supplied
warrant standard. The bare existence of a reason carries no such bridge. -/
def EligibleReasonUptakeWarrants {Agent Claim : Type}
    (Reason Believes Eligible Warrant : Agent → Claim → Prop) : Prop :=
  ∀ a p, Reason a p → Believes a p → Eligible a p → Warrant a p

/-- A reason and an actual belief can both be present while no belief is
warranted, even if eligible reason uptake would warrant it. -/
def JustificationOmissionControl : Prop :=
  ∃ Reason Believes Eligible Warrant : Unit → Unit → Prop,
    ThereAreEpistemicReasons Reason ∧ Believes () () ∧
      EligibleReasonUptakeWarrants Reason Believes Eligible Warrant ∧
      ¬ SomeEligibleReasonUptake Reason Believes Eligible ∧ NoJustifiedBeliefs Believes Warrant

/-- At least three quarters of the entries of a nonempty supplied benchmark
list receive correct binary answers. Repetitions count separately. No
sampling, normative warrant or transfer beyond the list is built in. -/
def ReliableOnBenchmark {State : Type} (benchmark : List State)
    (truth output : State → Bool) : Prop :=
  benchmark ≠ [] ∧ 3 * benchmark.length ≤ 4 * (benchmark.countP (fun s => truth s == output s))

/-- No method in the supplied method class clears the supplied benchmark. -/
def AllReasoningUnreliable {Method State : Type} (benchmark : List State)
    (truth : State → Bool) (output : Method → State → Bool) : Prop :=
  ∀ m, ¬ ReliableOnBenchmark benchmark truth (output m)

/-- A supplied method clears the benchmark. -/
def SomeReliableReasoning {Method State : Type} (benchmark : List State)
    (truth : State → Bool) (output : Method → State → Bool) : Prop :=
  ∃ m, ReliableOnBenchmark benchmark truth (output m)

/-- The blanket benchmark unreliability thesis fails in the fixed profile. -/
def AllReasoningUnreliableFails {Method State : Type} (benchmark : List State)
    (truth : State → Bool) (output : Method → State → Bool) : Prop :=
  ¬ AllReasoningUnreliable benchmark truth output

/-- The binary answer to a fixed question never changes across supplied states
where the correct answer differs. This is an output condition, with no
causal or probabilistic interpretation built in. -/
def TruthInsensitive {State : Type} (truth output : State → Bool) : Prop :=
  ∀ s t, truth s ≠ truth t → output s = output t

/-- No supplied method changes its binary answer across any pair of states
where the correct answer differs. -/
def AllFormationTruthInsensitive {Method State : Type} (truth : State → Bool)
    (output : Method → State → Bool) : Prop :=
  ∀ m, TruthInsensitive truth (output m)

/-- A method answers correctly in two supplied states with opposite truths. -/
def SomeOppositeTruthsAnsweredCorrectly {Method State : Type} (truth : State → Bool)
    (output : Method → State → Bool) : Prop :=
  ∃ m s t, truth s ≠ truth t ∧ output m s = truth s ∧ output m t = truth t

/-- The blanket output-insensitivity thesis fails for the supplied profile. -/
def AllFormationTruthInsensitiveFails {Method State : Type} (truth : State → Bool)
    (output : Method → State → Bool) : Prop :=
  ¬ AllFormationTruthInsensitive truth output

/-- The single-method constant profile clears the benchmark [true, true,
true, false] while being truth-insensitive and answering incorrectly at
false. The opposite-answer profile changes with truth and fails the
benchmark. -/
def AccuracyResponsivenessControls : Prop :=
  (SomeReliableReasoning [true, true, true, false] id (fun (_ : Unit) _ => true) ∧
    AllFormationTruthInsensitive id (fun (_ : Unit) _ => true) ∧
    (fun (_ : Bool) => true) false ≠ (id : Bool → Bool) false) ∧
  (AllReasoningUnreliable [true, true, true, false] id (fun (_ : Unit) s => !s) ∧
    AllFormationTruthInsensitiveFails id (fun (_ : Unit) s => !s))

/-- No premise set in this fixed semantic profile entails any content. This
includes singleton identity sequents. -/
def NoValidInference {World Claim : Type} (S : Semantics World Claim) : Prop :=
  ∀ Γ p, ¬ Entails S Γ p

/-- The global denial of semantic entailment fails in the fixed profile. -/
def NoValidInferenceFails {World Claim : Type} (S : Semantics World Claim) : Prop :=
  ¬ NoValidInference S

/-- A world in which a Bool content holds exactly if it is true. -/
def booleanProfile : Semantics Unit Bool where
  trueAt := fun _ p => p = true
  neg := Bool.not
  neg_true_iff := by intro _ p; cases p <;> decide

/-- A fixed inhabited profile validates the identity inference with the true
content and invalidates the inference from the true to the false content. -/
def ValidityControl : Prop :=
  Entails booleanProfile (fun p => p = true) true ∧
    ¬ Entails booleanProfile (fun p => p = true) false

/-- Weak reading: every known content has a supplied earlier demonstration
certificate, which may use no already known premise. Timing and correctness
of certificates belong to the interpretation of Demonstrated. -/
def WeakPriorDemonstration {Agent Claim : Type}
    (Knows Demonstrated : Agent → Claim → Prop) : Prop :=
  ∀ a p, Knows a p → Demonstrated a p

/-- Strong reading: in addition to the certificate, at least one premise
actually used by the agent is known and strictly prior on the supplied
dependency relation. Well-foundedness of that relation is separate. -/
def StrongPriorDemonstration {Agent Claim : Type}
    (Knows Demonstrated : Agent → Claim → Prop) (Prior : Claim → Claim → Prop)
    (Uses : Agent → Claim → Claim → Prop) : Prop :=
  ∀ a p, Knows a p → Demonstrated a p ∧ ∃ q, Uses a q p ∧ Prior q p ∧ Knows a q

/-- Accessibility of the supplied strict-priority relation at every content. -/
def WellFoundedDemonstrativePriority {Claim : Type} (Prior : Claim → Claim → Prop) : Prop :=
  WellFounded Prior

/-- No agent knows any member of the supplied content domain. The denial need
not be a member of this domain. -/
def NoKnownContent {Agent Claim : Type} (Knows : Agent → Claim → Prop) : Prop :=
  ∀ a p, ¬ Knows a p

/-- The sole content is known and has a certificate but no earlier premise is
used or prior. In the second profile all indexed contents are true and known,
have certificates, and use the next natural-number index as a prior premise.
Priority is irreflexive and transitive but fails well-foundedness. -/
def DemonstrationControls : Prop :=
  (∃ (Knows Demonstrated : Unit → Unit → Prop) (Prior : Unit → Unit → Prop)
      (Uses : Unit → Unit → Unit → Prop),
      Knows () () ∧ WeakPriorDemonstration Knows Demonstrated ∧
        WellFoundedDemonstrativePriority Prior ∧
        ¬ StrongPriorDemonstration Knows Demonstrated Prior Uses) ∧
  (∃ (Knows Demonstrated : Unit → Nat → Prop) (Prior : Nat → Nat → Prop)
      (Uses : Unit → Nat → Nat → Prop) (Holds : Nat → Prop),
      Knows () 0 ∧ (∀ a p, Knows a p → Holds p) ∧
        (∀ p, ¬ Prior p p) ∧ (∀ p q r, Prior p q → Prior q r → Prior p r) ∧
        StrongPriorDemonstration Knows Demonstrated Prior Uses ∧
        ¬ WellFoundedDemonstrativePriority Prior)

end TruthCore.Logic.EpistemicUnderminers
