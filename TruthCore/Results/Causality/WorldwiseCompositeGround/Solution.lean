module

public import TruthCore.Causality.WorldwiseCompositeGround

@[expose] public section
namespace TruthCore.Results.Causality.WorldwiseCompositeGround
open TruthCore.Causality.WorldwiseCompositeGround
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Mereology.UniversalFusionBoundary (Overlap Fusion)
open TruthCore.Mereology.SupplementationFusion (StrongSupplementation)

private def rank : Body → Nat
  | .whole => 0
  | .atom _ _ => 1

private theorem supportWF (w : Bool) : WellFounded (profile.grounds w) := by
  refine Subrelation.wf (r := (measure rank).rel) ?_ (measure rank).wf
  intro x y h
  rcases h with ⟨rfl, slot, rfl⟩
  exact Nat.zero_lt_succ 0

private theorem atomProper (w slot : Bool) : actualProperPart w (.atom w slot) .whole :=
  ⟨⟨rfl, True.intro, fun _ _ => True.intro⟩, by intro h; cases h⟩

private theorem atomContingent (w slot : Bool) :
    ContingentAt profile.ontic w (.atom w slot) := by
  refine ⟨rfl, !w, True.intro, ?_⟩
  cases w <;> intro h <;> cases h

private theorem atomLe (w slot : Bool) (x : Actual w)
    (h : slot ∈ (content x.val).val) : atomAt w slot ≤ x := by
  change ({slot} : Set Bool) ⊆ (content x.val).val
  intro b hb
  have heq : b = slot := hb
  cases heq
  exact h

private theorem allBelowWhole (w : Bool) (x : Actual w) : x ≤ wholeAt w :=
  fun _ _ => True.intro

/-- Same direct support as the main certificate; whole-first support rejects
reverse constituent-to-whole priority, rather than identifying it with parts. -/
theorem noIncomingWhole (w : Bool) (x : Body) : ¬ profile.grounds w x .whole := by
  rintro ⟨_, slot, h⟩
  cases h

private theorem actualStrong (w : Bool) : StrongSupplementation (Actual w) := by
  classical
  intro x y hnot
  change ¬ (content x.val).val ⊆ (content y.val).val at hnot
  obtain ⟨slot, hx, hy⟩ := Set.not_subset.mp hnot
  refine ⟨atomAt w slot, atomLe w slot x hx, ?_⟩
  rintro ⟨z, hza, hzy⟩
  obtain ⟨b, hb⟩ := (content z.val).property
  have heq : b = slot := hza hb
  exact hy (heq ▸ hzy hb)

private theorem actualFusion (w : Bool) : Fusion (pair w) (wholeAt w) := by
  refine ⟨fun x _ => allBelowWhole w x, ?_⟩
  intro p _
  obtain ⟨slot, hp⟩ := (content p.val).property
  cases slot with
  | false => exact ⟨atomAt w false, Or.inl rfl, atomAt w false,
      atomLe w false p hp, le_refl _⟩
  | true => exact ⟨atomAt w true, Or.inr rfl, atomAt w true,
      atomLe w true p hp, le_refl _⟩

private theorem actualDisjoint (w : Bool) : ¬ Overlap (atomAt w false) (atomAt w true) := by
  rintro ⟨z, hz0, hz1⟩
  obtain ⟨b, hb⟩ := (content z.val).property
  have h0 : b = false := hz0 hb
  have h1 : b = true := hz1 hb
  cases h0.symm.trans h1

private theorem properIsAtom (w : Bool) (x : Body) (h : actualProperPart w x .whole) :
    ∃ slot, x = .atom w slot := by
  cases x with
  | whole => exact False.elim (h.2 rfl)
  | atom c slot =>
    have hc : c = w := h.1.1
    cases hc
    exact ⟨slot, rfl⟩

theorem checks : ReplacementCertificate := by
  have p2 : ∀ w, EveryContingentGroundedAt profile w := by
    intro w x _ he hc
    cases x with
    | whole =>
      obtain ⟨_, v, _, hv⟩ := hc
      exact False.elim (hv True.intro)
    | atom c slot =>
      change c = w at he
      cases he
      exact ⟨.whole, True.intro, True.intro, rfl, slot, rfl⟩
  have endpoints : ∀ w c x, profile.ontic.Causes w c x →
      existsAt w c ∧ existsAt w x := by
    rintro w c x ⟨rfl, slot, rfl⟩
    exact ⟨True.intro, rfl⟩
  have intended : ∃ p : IntendedProfile Bool Body,
      p.underlying = profile ∧ (∀ x, ¬ p.abstract x) ∧
      (∀ w x, p.hasCausalPower w x ↔ x = .whole) ∧
      (∀ w, P2At p w ∧ P3At p w) := by
    refine ⟨{
      underlying := profile
      abstract := fun _ => False  -- category-constant: intended (no abstract candidate; meets the #1094 contract but supplies no Anchors, so not an intended interpretation under #1103)
      hasCausalPower := fun _ x => x = .whole
      disjoint := fun _ h => h.elim
      powerExists := ?_
      causalEndpoints := endpoints
      exerciseHasPower := fun _ _ _ h => h.1
      powerConcrete := fun _ _ _ => True.intro }, rfl, ?_, ?_, ?_⟩
    · intro w x h
      cases h
      exact True.intro
    · exact fun _ h => h.elim
    · exact fun _ _ => Iff.rfl
    · exact fun w => ⟨p2 w, supportWF w⟩
  have noNecessaryPart : ¬ ∃ x, (∃ w, actualProperPart w x .whole) ∧
      NecessaryAt profile.ontic false x := by
    rintro ⟨x, ⟨w, hx⟩, hn⟩
    obtain ⟨slot, rfl⟩ := properIsAtom w x hx
    obtain ⟨_, v, hv, hnExists⟩ := atomContingent w slot
    exact hnExists (hn v hv)
  have noFixedPart : ¬ ∃ x, ∀ w, actualProperPart w x .whole := by
    rintro ⟨x, h⟩
    obtain ⟨a, ha⟩ := properIsAtom false x (h false)
    obtain ⟨b, hb⟩ := properIsAtom true x (h true)
    cases ha.symm.trans hb
  refine ⟨intended, ?_, ?_, ?_, ?_, noNecessaryPart, noFixedPart, ?_⟩
  · exact fun _ => ⟨True.intro, True.intro, fun _ _ => True.intro⟩
  · exact fun w slot => ⟨atomProper w slot, atomContingent w slot, rfl, slot, rfl⟩
  · exact fun w => ⟨actualStrong w, actualFusion w, actualDisjoint w⟩
  · intro w x y
    exact ⟨fun h => ⟨x.property, y.property, h⟩, fun h => h.2.2⟩
  · exact fun w x _ => noIncomingWhole w x

end TruthCore.Results.Causality.WorldwiseCompositeGround
