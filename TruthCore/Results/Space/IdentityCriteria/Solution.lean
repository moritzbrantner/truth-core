module

public import TruthCore.Space.IdentityCriteria

@[expose] public section
namespace TruthCore.Results.Space.IdentityCriteria
open TruthCore.Space.IdentityCriteria

theorem relational_refl {C B R : Type} (s : SpatialData C B R) (x : C) :
    RelationalIdentity s x x := by
  refine ⟨1, ?_⟩
  intro r bs
  simp

theorem quotient_iff (G : Type) {C : Type} [Group G] [MulAction G C] (x y : C) :
    QuotientIdentity G x y ↔ ∃ g : G, g • y = x :=
  Quotient.eq

theorem quotient_to_relational {G C B R : Type} [Group G] [MulAction G C]
    (s : SpatialData C B R) (h : DataPreserved (G := G) s) (x y : C)
    (q : QuotientIdentity G x y) : RelationalIdentity s x y := by
  obtain ⟨g, rfl⟩ := (quotient_iff G x y).mp q
  exact h g y

theorem relational_to_quotient {G C B R : Type} [Group G] [MulAction G C]
    (s : SpatialData C B R) (h : OrbitComplete G s) (x y : C)
    (r : RelationalIdentity s x y) : QuotientIdentity G x y :=
  (quotient_iff G x y).mpr (h x y r)

theorem marker_alike (x y : Bool) : RelationalIdentity marker x y := by
  refine ⟨⟨Equiv.swap x y, Subgroup.mem_top _⟩, ?_⟩
  intro r bs
  change bs = [x] ↔ bs.map (Equiv.swap x y) = [y]
  constructor
  · rintro rfl
    simp
  · intro h
    have h' := congrArg (List.map (Equiv.swap x y)) h
    simpa [List.map_map, Function.comp_def] using h'

theorem marker_preserved (G : Type) [Group G] [MulAction G Bool] :
    DataPreserved (G := G) marker := fun _ _ => marker_alike _ _

theorem marker_complete : OrbitComplete (Equiv.Perm Bool) marker := by
  intro x y _
  exact ⟨Equiv.swap y x, by simp⟩

theorem fixed_complete (G : Type) [Group G] [MulAction G Bool] :
    OrbitComplete G fixedMarker := by
  rintro x y ⟨e, h⟩
  have he : e.val = 1 := Subgroup.mem_bot.mp e.property
  have xy := (h () [x]).mp rfl
  change List.map e.val [x] = [y] at xy
  have hxy : x = y := by simpa [he] using xy
  exact ⟨1, by simpa using hxy.symm⟩

theorem fixed_trivial : OrbitTrivial FixedTransforms Bool := by
  intro g x
  have ge : g.val = 1 := Subgroup.mem_bot.mp g.property
  change g.val x = x
  simp [ge]

theorem fixed_preserved : DataPreserved (G := FixedTransforms) fixedMarker := by
  intro g x
  rw [fixed_trivial g x]
  exact relational_refl _ _

theorem all_perms_quotient : QuotientIdentity (Equiv.Perm Bool) false true := by
  apply (quotient_iff _ _ _).mpr
  exact ⟨Equiv.swap false true, by simp⟩

theorem fixed_not_quotient : ¬ QuotientIdentity FixedTransforms false true := by
  intro h
  obtain ⟨g, hg⟩ := (quotient_iff _ _ _).mp h
  have ge : g.val = 1 := Subgroup.mem_bot.mp g.property
  change g.val true = false at hg
  rw [ge] at hg
  cases hg

theorem fixed_not_relational : ¬ RelationalIdentity fixedMarker false true := by
  rintro ⟨e, h⟩
  have he : e.val = 1 := Subgroup.mem_bot.mp e.property
  have bad := (h () [false]).mp rfl
  change List.map e.val [false] = [true] at bad
  rw [he] at bad
  simp at bad

/-- Conditional comparison, passive transport and separating/nonvacuity
controls. No original-sense mapping or complete-physics premise is proved. -/
theorem identity_criteria : Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨marker_preserved _, marker_alike _ _, fixed_not_quotient⟩,
    ⟨marker_preserved _, marker_complete, all_perms_quotient, by
      change false ≠ true
      decide⟩,
    ⟨fixed_complete _, all_perms_quotient, fixed_not_relational⟩,
    ⟨fixed_preserved, fixed_complete _, fixed_trivial,
      rfl, relational_refl fixedMarker false, rfl⟩⟩
  · intro G C B R _ _ s x y h
    cases h
    exact ⟨rfl, relational_refl s x⟩
  · intro G C B R _ _ s h x y q
    exact quotient_to_relational s h x y q
  · intro G C B R _ _ s h x y r
    exact relational_to_quotient s h x y r
  · intro G C B R _ _ s hp hc ht x y
    have rq : RelationalIdentity s x y ↔ QuotientIdentity G x y :=
      ⟨relational_to_quotient s hc x y, quotient_to_relational s hp x y⟩
    have qe : QuotientIdentity G x y ↔ RepresentedIdentity x y := by
      constructor
      · intro q
        obtain ⟨g, hg⟩ := (quotient_iff G x y).mp q
        exact hg.symm.trans (ht g y)
      · intro h
        cases h
        rfl
    refine ⟨rq, qe, ?_⟩
    intro k
    cases k with
    | relational => exact rq.trans qe
    | quotient => exact qe
    | represented => exact Iff.rfl
  · intro G C D B R _ _ s chart x y
    refine ⟨?_, ?_, ?_⟩
    · simp only [RelationalIdentity, reencode, Equiv.symm_apply_apply]
    · simp only [ChartQuotientIdentity, QuotientIdentity, Quotient.eq,
        Setoid.comap_rel, Equiv.symm_apply_apply]
    · exact chart.injective.eq_iff
end TruthCore.Results.Space.IdentityCriteria
