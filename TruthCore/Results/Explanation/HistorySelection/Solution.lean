import TruthCore.Explanation.HistorySelection
import TruthCore.Results.Causality.UniqueFeedback.Solution
import TruthCore.Results.Causality.EssentialPowerUnderdetermined.Solution
import TruthCore.Results.Causality.SourceWitness.Solution

namespace TruthCore.Results.Explanation.HistorySelection
open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive

theorem evidence_refl (truth : W → R → Prop) (basis : R → Prop) (w : W) :
    SameEvidence truth basis w w := fun _ _ => Iff.rfl

theorem evidence_trans (truth : W → R → Prop) (basis : R → Prop)
    (hvw : SameEvidence truth basis v w) (hwu : SameEvidence truth basis w u) :
    SameEvidence truth basis v u := fun r hr => (hvw r hr).trans (hwu r hr)

theorem characterization (h : History W B T) (truth : W → R → Prop)
    (basis : R → Prop) (a : W) :
    Determines h truth basis a ↔
      ∃ p, EvidenceOnly truth basis p ∧ Selects h p a := by
  constructor
  · intro hd
    refine ⟨fun w => SameEvidence truth basis w a, ?_, evidence_refl truth basis a, ?_⟩
    · intro v w hvw
      constructor
      · intro hva
        exact evidence_trans truth basis (fun r hr => (hvw r hr).symm) hva
      · exact evidence_trans truth basis hvw
    · exact hd
  · rintro ⟨p, hp, hselect⟩ v hv he
    exact hselect.2 v hv ((hp v a he).mpr hselect.1)

/-- Even the whole vector, under arbitrary infinitary recombination, cannot
supply an entailing discriminator when an accessible rival shares it. -/
theorem no_selection (h : History W B T) (truth : W → R → Prop)
    (basis : R → Prop) (a v : W) (hv : h.ontic.frame.access a v)
    (different : ¬ SameHistory h v a) (he : SameEvidence truth basis v a) :
    ¬ ∃ p, EvidenceOnly truth basis p ∧ Selects h p a := by
  intro hs
  exact different ((characterization h truth basis a).mpr hs v hv he)

theorem constant_failure :
    ¬ Determines chains (reasons false).reasonPresent (fun _ => True) false := by
  intro hd
  exact distinct_histories (hd true trivial (fun _ _ => Iff.rfl))

theorem rooted_failure :
    ¬ Determines rooted (reasons false).reasonPresent (fun _ => True) false := by
  exact constant_failure

theorem internal_success :
    Determines chains (reasons true).reasonPresent (fun _ => True) false := by
  intro v _ he
  have hv : false = v := (he false trivial).mpr rfl
  subst v
  intro _ _
  rfl

theorem rooted_source (w : Bool) :
    ∃ s, rooted.ontic.ExistsAt w s ∧
      (∀ y, ¬ rooted.ontic.Causes w y s) ∧
      ∀ x, rooted.ontic.ExistsAt w x → x ≠ s → rooted.ontic.Causes w s x := by
  refine ⟨(w, 0), rfl, ?_, ?_⟩
  · intro y hy
    exact hy.2.2 rfl
  · rintro ⟨b, n⟩ hb hne
    refine ⟨rfl, hb, ?_⟩
    intro hn
    exact hne (Prod.ext hb hn)

/-- Compose the old all-on/off, unique-feedback and source+infinite-branch
certificates. Uniqueness is derived pointwise, without an initial time/value.
The symmetric grounded and ungrounded cases share the entire presence arena. -/
theorem certificate : Certificate := by
  refine ⟨fun _ _ _ _ => characterization, fun _ _ _ _ => no_selection,
    TruthCore.Results.Causality.EssentialPowerUnderdetermined.essentialPowerUnderdetermined,
    ?_, ?_, ?_, ⟨constant_failure, rooted_failure⟩, rooted_source,
    ⟨internal_success, internal_success⟩,
    TruthCore.Results.Causality.SourceWitness.overlap_control⟩
  · have hu := TruthCore.Results.Causality.UniqueFeedback.controls
    refine ⟨fun _ => hu.2.1, ?_⟩
    intro signal hs
    exact funext (fun t => hu.2.2 (signal t) (hs t))
  · intro t
    exact ⟨t - 1, by omega⟩
  · intro t
    exact ⟨rfl, fun hs => hs ⟨t + 1, rfl⟩, rfl⟩

end TruthCore.Results.Explanation.HistorySelection

namespace TruthCore.Results.Explanation.HistorySelection
open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive

theorem omissions : OmissionControls := by
  refine ⟨⟨?_, distinct_histories⟩, ?_, ⟨?_, ?_⟩,
    (fun _ _ hf => hf.elim), (fun hs => hs.1), ?_⟩
  · intro v hv _
    change false = v at hv
    subst v
    intro _ _
    rfl
  · intro _ _ _ _ _
    rfl
  · refine ⟨rfl, ?_⟩
    intro v _ hv
    subst v
    intro _ _
    rfl
  · intro hp
    have he : SameEvidence (reasons false).reasonPresent (fun _ => True) true false :=
      fun _ _ => Iff.rfl
    exact Bool.noConfusion ((hp true false he).mpr rfl)
  · decide
end TruthCore.Results.Explanation.HistorySelection
