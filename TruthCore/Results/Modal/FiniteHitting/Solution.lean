module

public import TruthCore.Modal.FiniteHitting.Vocabulary
public import TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverLaws.Solution
public import TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverControls.Solution
public import TruthCore.Results.Logic.LimitAdmission.Solution
public import TruthCore.Results.Modal.PopulationClosureSeparation.Solution

@[expose] public section
namespace TruthCore.Results.Modal.FiniteHitting
open TruthCore.Modal.FiniteHitting
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)
open Filter Topology
open TruthCore.Logic.LimitAdmission

/-- Reuse the certified finite omission induction; classical negated necessity
provides each individual's absence witness. -/
theorem omission {W I : Type} (p : ExistsAt W I) (w : W)
    (ha : AbsenceAmalgamation (component W) p w)
    (hn : ¬ DeRe (component W) p w) : FiniteOmission p := by
  classical
  have hc : IndividualContingency (component W) p w := by
    intro x
    have hx : ∃ v, ¬ p x v := by
      by_contra h
      exact hn ⟨x, fun v _ => not_not.mp (not_exists.mp h v)⟩
    obtain ⟨v, hv⟩ := hx
    exact ⟨v, trivial, hv⟩
  intro xs
  obtain ⟨v, _, hv⟩ :=
    TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverLaws.checks.1
      W I (component W) p w ⟨w, trivial⟩ ha hc xs
  exact ⟨v, hv⟩

theorem hitting_deRe {W I : Type} (p : ExistsAt W I) (w : W)
    (hh : Hitting p) (ha : AbsenceAmalgamation (component W) p w) :
    DeRe (component W) p w := by
  classical
  by_contra hn
  obtain ⟨xs, hxs⟩ := hh
  obtain ⟨v, hv⟩ := omission p w ha hn xs
  obtain ⟨x, hx, hp⟩ := hxs v
  exact hv x hx hp

theorem oneFinite_hitting {W I : Type} (p : ExistsAt W I) (w : W)
    (hp : DeDicto (component W) p w)
    (ha : AbsenceAmalgamation (component W) p w) (ho : OneFinite p) : Hitting p := by
  classical
  obtain ⟨u, hu⟩ := ho
  refine ⟨hu.toFinset.toList, fun v => ?_⟩
  obtain ⟨z, _, hz⟩ := ha u v trivial trivial
  obtain ⟨x, hx⟩ := hp z trivial
  exact ⟨x, by simpa using (hz x hx).1, (hz x hx).2⟩

theorem oneFinite_deRe {W I : Type} (p : ExistsAt W I) (w : W)
    (hp : DeDicto (component W) p w)
    (ha : AbsenceAmalgamation (component W) p w) (ho : OneFinite p) :
    DeRe (component W) p w := hitting_deRe p w (oneFinite_hitting p w hp ha ho) ha

theorem finiteWorlds_deRe {W I : Type} [Finite W] (p : ExistsAt W I) (w : W)
    (hp : DeDicto (component W) p w)
    (ha : AbsenceAmalgamation (component W) p w) : DeRe (component W) p w := by
  classical
  let := Fintype.ofFinite W
  choose f hf using fun v => hp v trivial
  apply hitting_deRe p w _ ha
  refine ⟨(Finset.univ.image f).toList, fun v => ⟨f v, ?_, hf v⟩⟩
  simp

theorem survivor {W I : Type} (p : ExistsAt W I) (w : W)
    (hp : DeDicto (component W) p w)
    (ha : AbsenceAmalgamation (component W) p w)
    (hn : ¬ DeRe (component W) p w) : Survivor p := by
  classical
  refine ⟨fun hh => hn (hitting_deRe p w hh ha), ?_, ?_, omission p w ha hn, ?_⟩
  · intro v hv
    exact hn (oneFinite_deRe p w hp ha ⟨v, hv⟩)
  · exact not_finite_iff_infinite.mp (fun h => by
      let := h
      exact hn (finiteWorlds_deRe p w hp ha))
  · rintro ⟨v, hv⟩
    obtain ⟨x, hx⟩ := hp v trivial
    exact hv x hx

theorem laws : TruthCore.Modal.FiniteHitting.Laws :=
  ⟨fun _ _ => hitting_deRe, fun _ _ => oneFinite_hitting,
    fun _ _ => oneFinite_deRe, fun _ _ _ => finiteWorlds_deRe, fun _ _ => survivor⟩

/-- Mathlib finite open subcover of the existence cylinders. -/
theorem compact_hitting {I : Type} (S : Set (I → Bool)) (hk : IsCompact S)
    (hp : ∀ v : S, ∃ x, profilePresent S x v) : Hitting (profilePresent S) := by
  classical
  let U : I → Set (I → Bool) := fun x => {v | v x = true}
  have hopen : ∀ x, IsOpen (U x) := by
    intro x
    change IsOpen ((fun v : I → Bool => v x) ⁻¹' {b | b = true})
    exact (isOpen_discrete _).preimage (continuous_apply x)
  have hcover : S ⊆ ⋃ x, U x := by
    intro v hv
    obtain ⟨x, hx⟩ := hp ⟨v, hv⟩
    exact Set.mem_iUnion.mpr ⟨x, hx⟩
  obtain ⟨t, ht⟩ := hk.elim_finite_subcover U hopen hcover
  refine ⟨t.toList, fun v => ?_⟩
  obtain ⟨x, hx, hv⟩ := Set.mem_iUnion₂.mp (ht v.property)
  exact ⟨x, by simpa using hx, hv⟩

theorem compact_deRe {I : Type} (S : Set (I → Bool)) (w : S) (hk : IsCompact S)
    (hp : DeDicto (component S) (profilePresent S) w)
    (ha : AbsenceAmalgamation (component S) (profilePresent S) w) :
    DeRe (component S) (profilePresent S) w :=
  hitting_deRe _ w (compact_hitting S hk (fun v => hp v trivial)) ha

theorem not_compact {I : Type} (S : Set (I → Bool)) (w : S)
    (hp : DeDicto (component S) (profilePresent S) w)
    (ha : AbsenceAmalgamation (component S) (profilePresent S) w)
    (hn : ¬ DeRe (component S) (profilePresent S) w) : ¬ IsCompact S :=
  fun hk => hn (compact_deRe S w hk hp ha)

theorem compactLaws : CompactLaws :=
  ⟨fun _ => compact_hitting, fun _ => compact_deRe, fun _ => not_compact⟩

/-- Finite full cover implies a finite population at the designated world;
this direction needs neither necessary population nor amalgamation. -/
theorem cover_oneFinite {W I : Type} (p : ExistsAt W I) (w : W)
    (hf : FinitePopulationCover (component W) p w) : OneFinite p := by
  classical
  obtain ⟨xs, hx⟩ := hf
  exact ⟨w, (xs.toFinset.finite_toSet).subset (fun x hp => by simpa using hx w trivial x hp)⟩

theorem weakening : Weakening := by
  classical
  constructor
  · have hd : DeDicto (component Bool) finiteAndUnbounded false :=
      fun _ _ => ⟨0, Or.inr rfl⟩
    have ha : AbsenceAmalgamation (component Bool) finiteAndUnbounded false := by
      intro u v _ _
      refine ⟨false, trivial, ?_⟩
      intro x hx
      have h : x = 0 := by simpa [finiteAndUnbounded] using hx
      exact ⟨Or.inr h, Or.inr h⟩
    refine ⟨hd, ha, ⟨false, ?_⟩, ⟨[0], fun v => ⟨0, by simp, Or.inr rfl⟩⟩, ?_⟩
    · simp [finiteAndUnbounded]
    · rintro ⟨xs, hxs⟩
      have hall : (Set.univ : Set ℕ).Finite :=
        xs.toFinset.finite_toSet.subset (fun x _ => by simpa using hxs true trivial x (Or.inl rfl))
      exact Set.infinite_univ hall
  · constructor
    · have ha : AbsenceAmalgamation (component Bool) allInfinite false := by
        intro u v _ _
        refine ⟨true, trivial, ?_⟩
        intro x hx
        have h : 1 ≤ x := by simpa [allInfinite] using hx
        exact ⟨Or.inr h, Or.inr h⟩
      refine ⟨fun _ _ => ⟨1, Or.inr (by omega)⟩, ha,
        ⟨[1], fun v => ⟨1, by simp, Or.inr (by omega)⟩⟩, ?_⟩
      rintro ⟨v, hv⟩
      have hi : Set.Infinite {x : ℕ | 1 ≤ x} := Set.Ici_infinite 1
      exact hi (hv.subset (fun x hx => Or.inr hx))
    · exact fun _ _ => cover_oneFinite

/-- Tail noncompactness uses the previously certified CONVERGENCE theorem;
compact sets in the Hausdorff Bool product are closed. -/
theorem tailBoundary : TailBoundary := by
  have old := TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverControls.checks
  have h := old.2.1
  refine ⟨old, h.1, h.2.2.1, h.2.2.2.1, survivor _ 0 h.1 h.2.2.1 h.2.2.2.1, ?_⟩
  intro hk
  exact TruthCore.Results.Logic.LimitAdmission.false_not_tail
    (hk.isClosed.mem_of_tendsto TruthCore.Results.Logic.LimitAdmission.tail_tendsto
      (Eventually.of_forall fun n => Set.mem_range_self n))

/-- Singleton empty admissible profile: worlds inhabited, populations empty.
This deletion control is not advertised as a populated rival. -/
theorem empty_control :
    ∃ (I : Type) (S : Set (I → Bool)) (w : S), IsCompact S ∧
    AbsenceAmalgamation (component S) (profilePresent S) w ∧
    OneFinite (profilePresent S) ∧ ¬ DeDicto (component S) (profilePresent S) w ∧
    ¬ DeRe (component S) (profilePresent S) w := by
  let S : Set (Unit → Bool) := {fun _ => false}
  let w : S := ⟨fun _ => false, rfl⟩
  have absent : ∀ (v : S) x, ¬ profilePresent S x v := by
    intro v x
    have hv : v.val = fun _ => false := Set.mem_singleton_iff.mp v.property
    simp [profilePresent, hv]
  refine ⟨Unit, S, w, isCompact_singleton, ?_, ⟨w, Set.toFinite _⟩, ?_, ?_⟩
  · exact fun _ _ _ _ => ⟨w, trivial, fun x hx => (absent w x hx).elim⟩
  · intro hp
    obtain ⟨x, hx⟩ := hp w trivial
    exact absent w x hx
  · rintro ⟨x, hx⟩
    exact absent w x (hx w trivial)

/-- The EXISTING alternating existence predicate encoded as Bool profiles. -/
theorem alternating_control :
    ∃ (I : Type) (S : Set (I → Bool)) (w : S), IsCompact S ∧
    DeDicto (component S) (profilePresent S) w ∧ Hitting (profilePresent S) ∧
    OneFinite (profilePresent S) ∧ ¬ AbsenceAmalgamation (component S) (profilePresent S) w ∧
    ¬ DeRe (component S) (profilePresent S) w := by
  classical
  let f : Bool → Bool → Bool := fun v x => decide (alternatingExists x v)
  let S : Set (Bool → Bool) := Set.range f
  let w : S := ⟨f false, Set.mem_range_self _⟩
  have pop : ∀ v : S, ∃ x, profilePresent S x v := by
    rintro ⟨_, ⟨v, rfl⟩⟩
    exact ⟨v, by simp [profilePresent, f, alternatingExists]⟩
  have hn : ¬ DeRe (component S) (profilePresent S) w := by
    rintro ⟨x, hx⟩
    have h := hx ⟨f (!x), Set.mem_range_self _⟩ trivial
    cases x <;> simp [profilePresent, f, alternatingExists] at h
  have hh : Hitting (profilePresent S) := by
    refine ⟨[false, true], fun v => ?_⟩
    obtain ⟨x, hx⟩ := pop v
    exact ⟨x, by cases x <;> simp, hx⟩
  exact ⟨Bool, S, w, (Set.finite_range f).isCompact, fun v _ => pop v, hh,
    ⟨w, Set.toFinite _⟩, fun ha => hn (hitting_deRe _ w hh ha), hn⟩

/-- Singleton populated profile witnesses the positive compatible background
and deletion of ¬N in every core. -/
theorem positive_control :
    ∃ (I : Type) (S : Set (I → Bool)) (w : S), IsCompact S ∧
    DeDicto (component S) (profilePresent S) w ∧ Hitting (profilePresent S) ∧
    OneFinite (profilePresent S) ∧ AbsenceAmalgamation (component S) (profilePresent S) w ∧
    DeRe (component S) (profilePresent S) w := by
  let S : Set (Unit → Bool) := {fun _ => true}
  let w : S := ⟨fun _ => true, rfl⟩
  have present : ∀ (v : S) x, profilePresent S x v := by
    intro v x
    have hv : v.val = fun _ => true := Set.mem_singleton_iff.mp v.property
    simp [profilePresent, hv]
  exact ⟨Unit, S, w, isCompact_singleton, fun v _ => ⟨(), present v ()⟩,
    ⟨[()], fun v => ⟨(), by simp, present v ()⟩⟩, ⟨w, Set.toFinite _⟩,
    fun u v _ _ => ⟨w, trivial, fun x _ => ⟨present u x, present v x⟩⟩,
    ⟨(), fun v _ => present v ()⟩⟩

theorem omissionControls : OmissionControls :=
  ⟨empty_control, alternating_control, positive_control⟩

/-- Consume the existing certified strict closure separation unchanged. -/
theorem strictAmalgamation : TruthCore.Models.PopulationClosureSeparation.Separation :=
  TruthCore.Results.Modal.PopulationClosureSeparation.checks

theorem cores : Cores :=
  ⟨fun _ _ p w hh ha hn => hn (hitting_deRe p w hh ha),
    fun _ _ p w hp ha ho hn => hn (oneFinite_deRe p w hp ha ho),
    fun _ S w hp ha hk hn => hn (compact_deRe S w hk hp ha)⟩

theorem tailProfiles : TailProfiles := by
  let S := TruthCore.Logic.LimitAdmission.tailWorlds
  let w : S := ⟨tailProfile 0, Set.mem_range_self _⟩
  have hp : DeDicto (component S) (profilePresent S) w := by
    rintro ⟨_, ⟨n, rfl⟩⟩ _
    exact ⟨n, by simp [profilePresent, tailProfile]⟩
  have ha : AbsenceAmalgamation (component S) (profilePresent S) w := by
    rintro ⟨_, ⟨u, rfl⟩⟩ ⟨_, ⟨v, rfl⟩⟩ _ _
    refine ⟨⟨tailProfile (max u v), Set.mem_range_self _⟩, trivial, ?_⟩
    intro x hx
    have h : max u v ≤ x := by simpa [profilePresent, tailProfile] using hx
    constructor
    · simpa [profilePresent, tailProfile] using le_trans (le_max_left u v) h
    · simpa [profilePresent, tailProfile] using le_trans (le_max_right u v) h
  have hn : ¬ DeRe (component S) (profilePresent S) w := by
    rintro ⟨x, hx⟩
    have h := hx ⟨tailProfile (x + 1), Set.mem_range_self _⟩ trivial
    simp [profilePresent, tailProfile] at h
  exact ⟨w, hp, ha, hn, survivor _ w hp ha hn, tailBoundary.2.2.2.2.2⟩

/-- Profile-fixed registry form. Universal accessibility is an explicit
background premise, not silently inferred from S5. -/
theorem hittingCore (W I : Type) (F : TruthCore.Modal.Frame W) (p : ExistsAt W I) (w : W)
    (hu : TruthCore.Modal.S5Research.Universal F) (hh : Hitting p)
    (ha : AbsenceAmalgamation F p w) (hn : NoNecessary F p w) :
    TruthCore.Logic.ConfigurationFalse := by
  obtain ⟨x, hx⟩ := hitting_deRe p w hh
    (fun u v _ _ => by
      obtain ⟨z, _, hz⟩ := ha u v (hu w u) (hu w v)
      exact ⟨z, trivial, hz⟩)
  exact hn ⟨x, fun v _ => hx v trivial⟩

theorem finiteWorldCore (W I : Type) (F : TruthCore.Modal.Frame W) (p : ExistsAt W I) (w : W)
    (hu : TruthCore.Modal.S5Research.Universal F) (hp : DeDicto F p w)
    (ha : AbsenceAmalgamation F p w) (ho : OneFinite p) (hn : NoNecessary F p w) :
    TruthCore.Logic.ConfigurationFalse := by
  obtain ⟨x, hx⟩ := oneFinite_deRe p w (fun v _ => hp v (hu w v))
    (fun u v _ _ => by
      obtain ⟨z, _, hz⟩ := ha u v (hu w u) (hu w v)
      exact ⟨z, trivial, hz⟩) ho
  exact hn ⟨x, fun v _ => hx v trivial⟩

theorem checks : TruthCore.Modal.FiniteHitting.Package :=
  ⟨TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverLaws.checks,
    laws, compactLaws, weakening, tailBoundary, omissionControls,
    strictAmalgamation, cores, tailProfiles⟩
end TruthCore.Results.Modal.FiniteHitting
