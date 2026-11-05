module

public import TruthCore.Explanation.PSRLaterAxes
public import TruthCore.Results.Explanation.PSRStrength.Solution
public import TruthCore.Results.Explanation.PSRScope.Solution
public import TruthCore.Results.Explanation.PSRSelfApplication.Solution
public import TruthCore.Results.Explanation.ExplanatorySymmetry.Solution
public import TruthCore.Results.Explanation.ExplanatoryAdequacy.Solution
public import TruthCore.Results.Explanation.UltimateAdequacy.Solution
public import TruthCore.Results.Explanation.StoppingPoints.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.PSRLaterAxes

open TruthCore.Explanation.PSRStrength hiding ground
open TruthCore.Explanation.PSRSelfApplication hiding Fact groundInquiry
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.PSRLaterAxes
open TruthCore.Causality.DerivativeJointPower
open scoped ENNReal

namespace Old
abbrev strength := TruthCore.Results.Explanation.PSRStrength.strengthMap
abbrev collapse := TruthCore.Results.Explanation.PSRStrength.collapseCore
end Old

 theorem inquiry : InquiryAxis := by
  have bridge := TruthCore.Results.Explanation.PSRSelfApplication.bridgeLadder
  have forward := bridge.2.2.2.2.1
  have backward := bridge.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro W B F A I w hcov
    exact ⟨forward W B F A I w hcov, backward W B F A I w⟩
  · intro W B F A I w t c hcov htrack hsound hf hn hd hi ht hc
    have hp := forward W B F A I w hcov htrack
    exact TruthCore.Results.Explanation.PSRStrength.collapse_distribution A w t c
      hsound hf hn hd hi ht hc (fun ⟨f, hcf, hno⟩ => hno (hp f hcf))
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcritic, _⟩ :=
      TruthCore.Results.Explanation.PSRSelfApplication.stanceMap
    obtain ⟨_, _, _, _, _, _, _, hd, hh, _, _, _, _, hb, _, hs, _⟩ := hcritic
    exact ⟨hd, hh, hb, hs, fun hp => hb.2 (hp _ hb.1)⟩

 theorem contrast : ContrastAxis := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W B F A w S hu f hs hc v hv hn
    obtain ⟨r, hr, he, hall⟩ := hu f hs hc
    exact ⟨r, hr, he, hall v hv hn⟩
  · intro W B F A w S x hc hx hf hcontrast
    exact TruthCore.Results.Explanation.ExplanatoryAdequacy.core_contrast hc hx hf hcontrast
  · exact ⟨TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_closed,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_founded,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_two_way,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_no_contrast OneSource .target⟩
  · exact ⟨TruthCore.Results.Explanation.ExplanatoryAdequacy.chain_closed_whole,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.chain_contrast_whole,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.chain_not_uniform_whole⟩

 theorem chance_one {W B F : Type} (μ : PMF W) (A : Arena W B F) (r : F)
    (hr : ∀ w, A.holds w r) : chance μ A r = 1 :=
  (μ.toOuterMeasure_apply_eq_one_iff _).mpr (fun w _ => hr w)

 theorem condition_ubiquitous {W B F : Type} (μ : PMF W) (A : Arena W B F) (r f : F)
    (hr : ∀ w, A.holds w r) : chanceGiven μ A r f = chance μ A f := by
  unfold chanceGiven
  rw [chance_one μ A r hr, div_one]
  congr 1
  ext w
  exact and_iff_right (hr w)

 theorem source_true (w : Nat) : ground.holds w (.source true) := Or.inl rfl

 theorem trial_target : chance trial ground .target = 3 / 4 := by
  unfold chance trial
  rw [PMF.toOuterMeasure_map_apply]
  simp [ground, rival, groundHolds]

 theorem trial_other : chance trial ground .other = 1 / 4 := by
  unfold chance trial
  rw [PMF.toOuterMeasure_map_apply]
  simp [ground, rival, groundHolds, Set.indicator_apply]

 theorem trial_ranking : chanceGiven trial ground (.source true) .other <
     chanceGiven trial ground (.source true) .target := by
  rw [condition_ubiquitous trial ground (.source true) .other source_true,
    condition_ubiquitous trial ground (.source true) .target source_true, trial_other, trial_target]
  exact (ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num)).mpr (by norm_num)

 theorem trial_selected : SelectedAt (chanceFrame trial ground) oneSource Rival 0 := by
  intro f g hf hg htrue hfalse
  cases hf <;> cases hg
  · exact absurd htrue hfalse
  · refine ⟨⟨.source true, rfl, source_true 0, rfl, hfalse,
      GroundReason.toTarget true (Or.inl rfl), trial_ranking⟩, ?_⟩
    intro s hs _ hrev
    cases hs
    exact lt_asymm trial_ranking hrev
  · exact False.elim (htrue rfl)
  · exact absurd htrue hfalse

 theorem trial_not_selected : ¬ SelectedAt (chanceFrame trial ground) oneSource Rival 1 := by
  intro hs
  exact TruthCore.Results.Explanation.ExplanatorySymmetry.core_pair
    (TruthCore.Results.Explanation.ExplanatorySymmetry.same_ground 0 1)
    (TruthCore.Results.Explanation.ExplanatorySymmetry.perReason_fixed ground _ oneSource)
    trial_selected hs
    (TruthCore.Results.Explanation.ExplanatorySymmetry.ground_exhaustive 1)
    (TruthCore.Results.Explanation.ExplanatorySymmetry.ground_exclusive 0)
    Rival.target rfl (fun h => Nat.noConfusion h)

 theorem probability : ProbabilityAxis := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W B F μ A r f hr
    refine ⟨chance_one μ A r hr, condition_ubiquitous μ A r f hr, ?_⟩
    intro h
    exact lt_irrefl _ ((condition_ubiquitous μ A r f hr) ▸ h.2)
  · intro W B F μ A base O a f _hpositive hbase hselect hexclusive hexhaustive hf
    exact TruthCore.Results.Explanation.ExplanatorySymmetry.core_necessary
      hbase (TruthCore.Results.Explanation.ExplanatorySymmetry.perReason_fixed A _ base)
      hselect hexclusive hexhaustive hf
  · refine ⟨chance_one trial ground (.source true) source_true, ?_, ?_, ?_,
      trial_selected, trial_not_selected, source_true 1,
      GroundReason.toOther true 1 (Or.inl rfl) (fun h => Nat.noConfusion h),
      (fun h => Nat.noConfusion h), (fun h => Nat.noConfusion h), ?_, ?_⟩
    · rw [condition_ubiquitous trial ground (.source true) .target source_true, trial_target]
    · rw [condition_ubiquitous trial ground (.source true) .other source_true, trial_other]
    · intro r hr
      cases hr
      rw [chance_one trial ground (.source true) source_true]
      exact zero_lt_one
    · rw [trial_other]
      exact ENNReal.div_pos one_ne_zero (by norm_num)
    · intro h
      have hlt := h.2
      rw [condition_ubiquitous trial ground (.source true) .target source_true] at hlt
      exact lt_irrefl _ hlt
  · refine ⟨?_, trivial, fun h => Nat.noConfusion h⟩
    unfold chance
    rw [PMF.toOuterMeasure_pure_apply]
    simp [ground, rival, groundHolds]

 theorem productive : ProductiveAxis := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨?_, TruthCore.Results.Explanation.ExplanatoryAdequacy.overlay_all_necessary k⟩
    intro f hc
    obtain ⟨_, v, _, hn⟩ := hc
    exact False.elim (hn (Or.inr (Or.inl rfl)))
  · refine ⟨?_, TruthCore.Results.Explanation.UltimateAdequacy.chain_no_supply 2⟩
    intro f _
    refine ⟨f + 1, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), f, trivial, rfl, ?_⟩
    exact Or.inl (Or.inl rfl)
  · exact TruthCore.Results.Explanation.UltimateAdequacy.single_supply 2
  · exact ⟨TruthCore.Results.Explanation.UltimateAdequacy.plural_supply 2,
      TruthCore.Results.Explanation.UltimateAdequacy.plural_no_least⟩
  · exact ⟨TruthCore.Results.Explanation.UltimateAdequacy.branch_least,
      TruthCore.Results.Explanation.UltimateAdequacy.branch_no_supply⟩

 theorem stopping : StoppingAxis := by
  obtain ⟨_, _, _, _, _, _, _, _, _, htwin, _, hground, _⟩ :=
    TruthCore.Results.Explanation.StoppingPoints.foundationNormTest
  exact ⟨⟨htwin.1, htwin.2.1, htwin.2.2.1⟩, hground.2.2.1, hground.2.2.2.1⟩

 theorem agency : AgencyBoundary := by
  have h := TruthCore.Results.Explanation.ExplanatorySymmetry.comparison.2.2.2.1
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, (h.2.2.2.2.2.2 True).2 trivial,
    fun hp => (h.2.2.2.2.2.2 False).1 hp⟩

/-- Certified composition; no probability score or support relation is promoted
to a production/adequacy premise. The positive-base side condition in the
probability row licenses conditional-probability interpretation; the order-theoretic
core used there is stronger and does not require it. -/
theorem interpretedMap : TruthCore.Explanation.PSRLaterAxes.InterpretedMap :=
  ⟨Old.strength, Old.collapse, TruthCore.Results.Explanation.PSRScope.psrScopeBoundary,
    inquiry, contrast, probability, productive, stopping, agency⟩

end TruthCore.Results.Explanation.PSRLaterAxes
