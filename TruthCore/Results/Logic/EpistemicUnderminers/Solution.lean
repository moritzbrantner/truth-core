module

public import TruthCore.Logic.EpistemicUnderminers
public import TruthCore.Results.Logic.EpistemicNihilismRetorsion.Solution

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicUnderminers

open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicUnderminers
open TruthCore.Logic.ReflectiveCoherence

theorem f6ExcludesNihilism {Agent Claim : Type} (Reason : Agent → Claim → Prop)
    (hReason : ThereAreEpistemicReasons Reason) : EpistemicNihilismFails Reason := by
  obtain ⟨a, p, hp⟩ := hReason
  intro hNone
  exact EpistemicNihilismRetorsion.nihilismSelfUndermining Reason p hNone a hp

theorem eligibleReasonUptakeYieldsWarrant {Agent Claim : Type}
    (Reason Believes Eligible Warrant : Agent → Claim → Prop)
    (hTaken : SomeEligibleReasonUptake Reason Believes Eligible)
    (hBridge : EligibleReasonUptakeWarrants Reason Believes Eligible Warrant) :
    SomeJustifiedBelief Believes Warrant := by
  obtain ⟨a, p, hr, hb, he⟩ := hTaken
  exact ⟨a, p, hb, hBridge a p hr hb he⟩

theorem justificationOmissionControl : JustificationOmissionControl := by
  refine ⟨fun _ _ => True, fun _ _ => True, fun _ _ => False, fun _ _ => False,
    ⟨(), (), trivial⟩, trivial, ?_, ?_, ?_⟩
  · exact fun _ _ _ _ h => h
  · exact fun ⟨_, _, _, _, h⟩ => h
  · exact fun ⟨_, _, _, h⟩ => h

theorem reliableWitnessExcludesUnreliability {Method State : Type} (benchmark : List State)
    (truth : State → Bool) (output : Method → State → Bool)
    (hReliable : SomeReliableReasoning benchmark truth output) :
    AllReasoningUnreliableFails benchmark truth output := by
  obtain ⟨m, hm⟩ := hReliable
  exact fun hNone => hNone m hm

theorem oppositeCorrectAnswersExcludeInsensitivity {Method State : Type} (truth : State → Bool)
    (output : Method → State → Bool)
    (hAnswers : SomeOppositeTruthsAnsweredCorrectly truth output) :
    AllFormationTruthInsensitiveFails truth output := by
  obtain ⟨m, s, t, hOpposite, hs, ht⟩ := hAnswers
  intro hInsensitive
  exact hOpposite (hs.symm.trans ((hInsensitive m s t hOpposite).trans ht))

theorem accuracyResponsivenessControls : AccuracyResponsivenessControls := by
  refine ⟨⟨⟨(), ?_⟩, fun _ _ _ _ => rfl, by decide⟩, ⟨?_, ?_⟩⟩
  · unfold ReliableOnBenchmark
    decide
  · rintro ⟨⟩
    unfold ReliableOnBenchmark
    decide
  · intro h
    exact Bool.false_ne_true (h () true false (by decide))

theorem identityExcludesNoValidInference {World Claim : Type} (S : Semantics World Claim)
    (p : Claim) : NoValidInferenceFails S := by
  intro hNone
  exact hNone (fun q => q = p) p (fun _ hp => hp p rfl)

theorem validityControl : ValidityControl := by
  refine ⟨fun _ hp => hp true rfl, ?_⟩
  intro h
  exact Bool.false_ne_true (h () (fun _ hp => hp))

theorem strongPriorImpliesWeak {Agent Claim : Type}
    (Knows Demonstrated : Agent → Claim → Prop) (Prior : Claim → Claim → Prop)
    (Uses : Agent → Claim → Claim → Prop)
    (hStrong : StrongPriorDemonstration Knows Demonstrated Prior Uses) :
    WeakPriorDemonstration Knows Demonstrated :=
  fun a p h => (hStrong a p h).1

theorem strongPriorExcludesKnowledge {Agent Claim : Type}
    (Knows Demonstrated : Agent → Claim → Prop) (Prior : Claim → Claim → Prop)
    (Uses : Agent → Claim → Claim → Prop)
    (hStrong : StrongPriorDemonstration Knows Demonstrated Prior Uses)
    (hFounded : WellFoundedDemonstrativePriority Prior) : NoKnownContent Knows := by
  intro a p
  induction p using hFounded.induction with
  | h p ih =>
    intro hp
    obtain ⟨_, q, _, hPrior, hKnown⟩ := hStrong a p hp
    exact ih q hPrior hKnown

theorem demonstrationControls : DemonstrationControls := by
  constructor
  · refine ⟨fun _ _ => True, fun _ _ => True, fun _ _ => False, fun _ _ _ => False,
      trivial, fun _ _ _ => trivial, ⟨fun p => Acc.intro p (fun _ h => h.elim)⟩, ?_⟩
    intro hStrong
    obtain ⟨_, _, hUsed, _, _⟩ := hStrong () () trivial
    exact hUsed
  · let Knows : Unit → Nat → Prop := fun _ _ => True
    let Demonstrated : Unit → Nat → Prop := fun _ _ => True
    let Prior : Nat → Nat → Prop := fun q p => p < q
    let Uses : Unit → Nat → Nat → Prop := fun _ q p => q = p + 1
    have hStrong : StrongPriorDemonstration Knows Demonstrated Prior Uses :=
      fun _ p _ => ⟨trivial, p + 1, rfl, Nat.lt_succ_self p, trivial⟩
    refine ⟨Knows, Demonstrated, Prior, Uses, fun _ => True, trivial, fun _ _ _ => trivial,
      fun p => Nat.lt_irrefl p, fun _ _ _ hpq hqr => Nat.lt_trans hqr hpq, hStrong, ?_⟩
    exact fun hFounded => strongPriorExcludesKnowledge Knows Demonstrated Prior Uses
      hStrong hFounded () 0 trivial

end TruthCore.Results.Logic.EpistemicUnderminers
