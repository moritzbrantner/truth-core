import TruthCore.Causality.AtomisticUniversalCausePriority
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Causality.AtomisticCausalSource.Solution

namespace TruthCore.Results.Causality.AtomisticUniversalCausePriority
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.AtomisticUniversalCausePriority

private theorem atomicParts {B : Type} [PartialOrder B]
    (hWF : ProperPartWF B) : AtomicParts B := by
  intro x
  obtain ⟨a, hax, hmin⟩ := hWF.has_min {p | p ≤ x} ⟨x, le_refl x⟩
  refine ⟨a, hax, ?_⟩
  intro b hba
  by_contra hn
  exact hmin b (le_trans hba hax) (lt_of_le_not_ge hba hn)

theorem causedSimplePart {B : Type} [PartialOrder B] (G : Graph B)
    (hWF : ProperPartWF B) (hP6 : CausedCompositeHasCausedProperPart G)
    (hEM : ExcludedMiddle) : EveryCausedObjectHasCausedSimplePart G := by
  intro x
  induction x using hWF.induction with
  | h x ih =>
    intro hx
    rcases hEM (TruthCore.Mereology.UniversalFusionBoundary.Composite x) with hc | hn
    · obtain ⟨p, hpx, hp⟩ := hP6 x hx hc
      obtain ⟨a, hap, ha, hca⟩ := ih p hpx hp
      exact ⟨a, le_trans hap hpx.le, ha, hca⟩
    · refine ⟨x, le_refl x, ?_, hx⟩
      intro p hp
      rcases hEM (x ≤ p) with hxp | hnxp
      · exact hxp
      · exact (hn ⟨p, lt_of_le_not_ge hp hnxp⟩).elim

theorem universalPriority {B : Type} [PartialOrder B] (G : Graph B)
    (Prior : B → B → Prop)
    (hPop : ObjectPopulation B) (hWF : ProperPartWF B)
    (hCover : ConditionalCausedSimpleCover G) (hNoOverlap : CauseEffectNonoverlap G)
    (hActivity : CausalActivity G) (hEM : ExcludedMiddle)
    (hP6 : CausedCompositeHasCausedProperPart G)
    (hCausePrior : CausePriorToEffectParts G Prior)
    (hPartPrior : ProperPartsPrior Prior)
    (hTrans : TransitiveExistentialPriority Prior) : UniversalCausePriority G Prior := by
  have hAtomic := atomicParts hWF
  have hExtract := causedSimplePart G hWF hP6 hEM
  obtain ⟨root, _, y, _, hry⟩ :=
    TruthCore.Results.Causality.AtomisticCausalSource.outgoing
      G hPop hAtomic hCover hNoOverlap hEM hActivity
  obtain ⟨a, _, ha, hca⟩ := hExtract y ⟨root, hry⟩
  obtain ⟨M, hM⟩ := hCover ⟨a, ha, hca⟩
  have hMNoOutput : ¬ ∃ z, G.edge M z := by
    rintro ⟨z, hmz⟩
    obtain ⟨p, hpz, hp, hcp⟩ := hExtract z ⟨M, hmz⟩
    exact hNoOverlap M z hmz ⟨p, hM p ⟨hp, hcp⟩, hpz⟩
  have hMcaused : ∃ N, G.edge N M := by
    rcases hActivity M with hi | ⟨z, _, ho⟩
    · exact hi
    · exact (hMNoOutput ⟨z, ho⟩).elim
  obtain ⟨N, hNM⟩ := hMcaused
  have hNsource : G.Source N := by
    intro hNcaused
    obtain ⟨p, hpN, hp, hcp⟩ := hExtract N hNcaused
    exact hNoOverlap N M hNM ⟨p, hpN, hM p ⟨hp, hcp⟩⟩
  refine ⟨N, M, hNsource, hNM, hM, ?_⟩
  intro x hx
  obtain ⟨p, hpx, hp, hcp⟩ := hExtract x hx
  have hNp := hCausePrior N M hNM p (hM p ⟨hp, hcp⟩)
  rcases hEM (p = x) with heq | hne
  · exact heq ▸ hNp
  · exact hTrans N p x hNp (hPartPrior p x (lt_of_le_of_ne hpx hne))

theorem consistency : TruthCore.Causality.AtomisticUniversalCausePriority.Consistency := by
  have old := TruthCore.Results.Causality.AtomisticCausalSource.consistency
  have hSimple := old.2.2.2.2.2.2.2.1
  have hNoLT : ∀ p x : TruthCore.Causality.AtomisticCausalSource.Fixture.Object, ¬ p < x := by
    intro p x h
    exact h.not_ge (hSimple x h.le)
  have hWF : ProperPartWF TruthCore.Causality.AtomisticCausalSource.Fixture.Object := by
    exact ⟨fun x => Acc.intro x (fun y hy => (hNoLT y x hy).elim)⟩
  have hCP : CausePriorToEffectParts TruthCore.Causality.AtomisticCausalSource.Fixture.graph Fixture.prior := by
    intro c e hce p hpe
    change p = e at hpe
    exact hpe ▸ hce
  have hPP : ProperPartsPrior Fixture.prior := by
    intro p x hpx
    exact (hNoLT p x hpx).elim
  have hTrans : TransitiveExistentialPriority Fixture.prior := by
    intro x y z hxy hyz
    have hbad := hxy.2.symm.trans hyz.1
    cases hbad
  have hIr : ∀ x, ¬ Fixture.prior x x := by
    intro x hx
    have hbad := hx.1.symm.trans hx.2
    cases hbad
  refine ⟨old, hWF, hCP, hPP, hTrans, hIr, ?_⟩
  refine ⟨.origin, .effect, ?_, ⟨rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    cases hc.2
  · rintro a ⟨_, c, hc⟩
    exact hc.2
  · rintro x ⟨c, hc⟩
    exact ⟨rfl, hc.2⟩

end TruthCore.Results.Causality.AtomisticUniversalCausePriority
