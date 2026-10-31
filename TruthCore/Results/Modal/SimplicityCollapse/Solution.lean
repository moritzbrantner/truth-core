import TruthCore.Modal.SimplicityCollapse
import TruthCore.Results.Modal.SelectedEffectBridge.Solution
import TruthCore.Results.Explanation.ExplanatorySymmetry.Solution

namespace TruthCore.Results.Modal.SimplicityCollapse
open TruthCore.Modal.SimplicityCollapse
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.PSRStrength hiding ground
open TruthCore.Case.Catholicism (IsImmutable)
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)

variable {W B A R F : Type}

/-! ## The core -/

theorem rigid_core (p : OutputProfile W B A) (w : W) (a : A) (x : B)
    (hSame : SameActEverywhere p w a) (hStrict : StrictEfficacy p w a x) :
    ¬ ContingentAt p.ontic w x := by
  rintro ⟨_, v, hv, hx⟩
  exact hx (hStrict v hv (hSame v hv))

/-- Same computation as `selectedEffectNecessary`, without its same-act premise. -/
theorem stable_strict (p : OutputProfile W B A) (w : W) (a : A) (x : B)
    (hSound : SoundDistinctCauses p.ontic) (hRealized : RealizedOutputs p)
    (hStable : StableActOutput p w a) (hActual : p.output w a x) : StrictEfficacy p w a x := by
  intro v hv hp
  exact (hSound v p.source x (hRealized v a x hp (hStable x hActual v hv hp))).2.1

theorem noCreation_contingent : ContingentAt noCreation false firstEffect := by
  refine ⟨Or.inr ⟨rfl, rfl⟩, true, trivial, ?_⟩
  rintro (h | ⟨_, h⟩)
  · cases h
  · cases h

theorem noCreation_necessary : NecessaryAt noCreation false source :=
  fun _ _ => Or.inl rfl

theorem exists_first {v : Bool} (h : noCreation.ExistsAt v firstEffect) : v = false := by
  rcases h with h | ⟨_, h⟩
  · cases h
  · exact h

theorem core : TruthCore.Modal.SimplicityCollapse.Core := by
  refine ⟨fun _ _ _ p w a x => rigid_core p w a x,
    fun _ _ _ p w a x => stable_strict p w a x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ p w a x ⟨_, v, hv, hx⟩
    by_cases hp : p.performs v a
    · exact Or.inr ⟨v, hv, hp, hx⟩
    · exact Or.inl ⟨v, hv, hp⟩
  · refine ⟨noCreation_necessary, rfl, ?_, ?_, noCreation_contingent⟩
    · intro h
      cases h true trivial
    · intro v _ hp
      exact Or.inr ⟨rfl, hp⟩
  · refine ⟨noCreation_necessary, trivial, fun _ _ => trivial, ?_, noCreation_contingent⟩
    intro h
    have := exists_first (h true trivial trivial)
    cases this
  · refine ⟨fixedSourceNecessaryAt, trivial, fun _ _ => trivial, ?_, ?_⟩
    · intro _ _ _
      exact Or.inr rfl
    · rintro ⟨_, v, _, hx⟩
      exact hx (Or.inr rfl)
  · intro _ _ _ p w a hN hC v hv
    exact hC v (hN v hv)
  · intro h
    cases h true (Or.inl rfl)
  · intro _ _ _ p d w a hS hR v hv
    exact hS v a (hR v hv)
  · refine ⟨?_, ?_, rfl, rfl⟩
    · intro v a h
      cases v with
      | false => rfl
      | true => cases h
    · intro v _ hx
      rw [exists_first hx]
      exact ⟨(), rfl⟩
  · refine ⟨?_, fun v _ => ⟨v, rfl⟩, ?_⟩
    · intro v a h
      exact (Option.some.inj h).symm
    · intro a h
      cases a with
      | false => cases h true trivial
      | true => cases h false trivial
  · rintro _ _ _ p w a _ x rfl hS hE
    exact rigid_core p w a x hS hE
  · refine ⟨fun _ _ => Or.inl rfl, ?_, noCreation_contingent, ?_, ?_⟩
    · intro v _ hp
      rcases hp with h | h
      · cases h
      · exact Or.inr ⟨rfl, h⟩
    · intro h
      have := exists_first (h true trivial (Or.inl rfl))
      cases this
    · intro h
      rcases h true trivial with h | h <;> cases h

/-! ## The root-route exposure -/

/-- The readings at `w` exclude a respect true at an accessible world and false at `w`. -/
theorem no_unrealized {m : Ontic W B} {InAct InPotency CanBe : W → B → R → Prop} {w v : W} {g : B}
    {r : R} (h : ReadingsAt m InAct InPotency CanBe w g) (hv : m.frame.access w v)
    (hr : InAct v g r) : InAct w g r := by
  obtain ⟨hP, hI, hC⟩ := h
  by_contra hn
  exact hI r ((hP g r).mpr ⟨hC v r hv hr, hn⟩)

theorem decree_collapse {m : Ontic W B} {InAct InPotency CanBe : W → B → R → Prop} {O : R → Prop}
    {w : W} {g x : B} {d : R} (h : ReadingsAt m InAct InPotency CanBe w g) (hO : O d)
    (hd : InAct w g d) (hE : ExclusiveDecree InAct O w g)
    (hS : ∀ v, m.frame.access w v → SomeDecree InAct O v g)
    (hR : RespectSuffices m InAct w g d x) : ¬ ContingentAt m w x := by
  rintro ⟨_, v, hv, hx⟩
  obtain ⟨e, hOe, he⟩ := hS v hv
  have hed : e = d := hE e d hOe hO (no_unrealized h hv he) hd
  subst hed
  exact hx (hR v hv he)

theorem bool_cases {P : Bool → Prop} (h0 : P false) (h1 : P true) : ∀ b, P b
  | false => h0
  | true => h1

theorem someDecree_label (v : Bool) : SomeDecree labelAct (fun _ => True) v source :=
  ⟨v, trivial, rfl⟩

theorem label_decreed : Decreed noCreation labelAct (fun _ => True) false source false firstEffect := by
  refine ⟨trivial, rfl, ?_, fun v _ => someDecree_label v, ?_, noCreation_contingent⟩
  · intro d e _ _ hd he
    exact hd.trans he.symm
  · intro v _ h
    exact Or.inr ⟨rfl, h.symm⟩

theorem reading_empty {R : Type} (Act Can : EffectBeing → R → Prop) (hCan : ∀ x r, Can x r → Act x r) :
    PotencyIsUnactualizedCapacityReading Act (fun _ _ => False) Can := by
  intro x r
  exact ⟨False.elim, fun ⟨hc, hn⟩ => hn (hCan x r hc)⟩

theorem immutable_empty {R : Type} : IsImmutable (fun (_ : EffectBeing) (_ : R) => False) source :=
  fun _ h => h

theorem readings_full {R : Type} (m : Ontic Bool EffectBeing) (Act : Bool → EffectBeing → R → Prop)
    (w : Bool) (hAct : ∀ x r, Act w x r) : ReadingsAt m Act noAbility fullAbility w source :=
  ⟨reading_empty _ _ (fun x r _ => hAct x r), immutable_empty, fun _ _ _ _ => trivial⟩

theorem false_ability_readings (m : Ontic Bool EffectBeing) (w : Bool) :
    ReadingsAt m constantAct noAbility falseAbility w source :=
  ⟨reading_empty _ _ (fun _ _ h => h), immutable_empty, fun _ _ _ h => h⟩

theorem constant_exclusive : ExclusiveDecree constantAct (fun _ => True) false source :=
  fun _ _ _ _ hd he => hd.trans he.symm

theorem actualOnly_readings : ReadingsAt noCreation actualOnlyAct actualOnlyPotency falseAbility false source := by
  refine ⟨fun _ _ => Iff.rfl, ?_, ?_⟩
  · rintro r ⟨hr, hn⟩
    exact hn ⟨rfl, hr⟩
  · rintro v r _ ⟨_, hr⟩
    exact hr

theorem rootExposure : RootExposure := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ h hv hr => no_unrealized h hv hr,
    fun _ _ _ _ _ _ _ _ _ _ _ _ h hO hd hE hS hR => decree_collapse h hO hd hE hS hR,
    fun _ _ _ _ _ _ _ _ _ _ _ h hv hr => no_unrealized h hv hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the fork
  · intro _ _ _ m InAct InPotency CanBe O w g x d hP hI hO hd hE hR hC
    by_cases hCap : ModalCapacity m InAct CanBe w g
    · left
      obtain ⟨_, v, hv, hx⟩ := hC
      refine ⟨v, hv, hx, ?_⟩
      rintro ⟨e, hOe, he⟩
      have hed : e = d := hE e d hOe hO (no_unrealized ⟨hP, hI, hCap⟩ hv he) hd
      subst hed
      exact hx (hR v hv he)
    · exact Or.inr hCap
  -- delete the potency reading
  · refine ⟨?_, immutable_empty, fun _ _ _ _ => trivial, label_decreed⟩
    intro h
    have : False := (h source true).mpr ⟨trivial, fun hb => by cases hb⟩
    exact this
  -- delete immutability
  · refine ⟨?_, ?_, fun _ _ _ _ => trivial, label_decreed⟩
    · intro x r
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    · intro h
      exact h true (fun hb => by cases hb)
  -- delete `ModalCapacity`
  · refine ⟨reading_empty _ _ (fun _ _ h => h.elim), immutable_empty, ?_, label_decreed⟩
    intro h
    exact h true true trivial rfl
  -- delete field membership
  · refine ⟨readings_full _ _ false (fun _ _ => Or.inl rfl), by simp, Or.inl rfl, ?_, ?_, ?_,
      noCreation_contingent⟩
    · intro d e hd he _ _
      exact hd.trans he.symm
    · intro v _
      exact ⟨true, rfl, Or.inr rfl⟩
    · rintro v _ (h | h)
      · exact Or.inr ⟨rfl, h⟩
      · cases h
  -- delete the actual decree
  · refine ⟨⟨reading_empty _ _ (fun _ _ h => h), immutable_empty, fun _ _ _ h => h⟩, by simp [otherAct], ?_, ?_, ?_,
      noCreation_contingent⟩
    · intro _ _ _ _ hd he
      exact hd.trans he.symm
    · intro _ _
      exact ⟨true, trivial, rfl⟩
    · intro _ _ h
      cases h
  -- delete exclusivity
  · refine ⟨readings_full _ _ false (fun _ _ => Or.inl rfl), Or.inl rfl, ?_, ?_, ?_,
      noCreation_contingent⟩
    · intro h
      have := h false true trivial trivial (Or.inl rfl) (Or.inl rfl)
      cases this
    · intro _ _
      exact ⟨true, trivial, Or.inr rfl⟩
    · rintro v _ (h | h)
      · exact Or.inr ⟨rfl, h⟩
      · cases h
  -- delete a decree at each accessible world
  · refine ⟨actualOnly_readings, ⟨rfl, rfl⟩, ?_, ?_, ?_, noCreation_contingent⟩
    · rintro _ _ _ _ ⟨_, hd⟩ ⟨_, he⟩
      exact hd.trans he.symm
    · rintro ⟨_, _, h, _⟩
      cases h
    · rintro v _ ⟨h, _⟩
      exact Or.inr ⟨rfl, h⟩
  -- delete sufficiency
  · refine ⟨false_ability_readings _ _, rfl, constant_exclusive, ?_, ?_, noCreation_contingent⟩
    · intro _ _
      exact ⟨false, trivial, rfl⟩
    · intro h
      have := exists_first (h true trivial rfl)
      cases this
  -- delete contingency
  · refine ⟨false_ability_readings _ _, rfl, constant_exclusive, ?_, ?_, ?_⟩
    · intro _ _
      exact ⟨false, trivial, rfl⟩
    · intro _ _ _
      exact Or.inr rfl
    · rintro ⟨_, v, _, hx⟩
      exact hx (Or.inr rfl)
  -- controls of the third clause
  · refine ⟨actualOnly_readings, ?_, noCreation_contingent⟩
    intro h
    refine h false ⟨rfl, ?_⟩
    rintro ⟨hb, _⟩
    cases hb
  · refine ⟨⟨reading_empty _ _ (fun _ _ h => h), immutable_empty, ?_⟩,
      ⟨reading_empty _ _ (fun _ _ h => h), immutable_empty, ?_⟩, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · rintro v r _ ⟨h, hr⟩
      exact ⟨rfl, hr⟩
    · intro _ _ h
      cases h
    · rintro ⟨h, _⟩
      cases h
    · intro h
      cases h
    · refine ⟨Or.inr ⟨rfl, rfl⟩, true, rfl, ?_⟩
      rintro (h | ⟨_, h⟩)
      · cases h
      · cases h
  -- no decree is a respect
  · refine ⟨readings_full _ _ false (fun _ _ => trivial), readings_full _ _ true (fun _ _ => trivial),
      fun _ => Iff.rfl, ?_, rfl, ?_, noCreation_contingent⟩
    · intro r h
      have := exists_first (h true trivial trivial)
      cases this
    · intro v _ hp
      rcases hp with h | h
      · cases h
      · exact Or.inr ⟨rfl, h⟩
  -- selection
  · intro _ _ _ X act O a h
    obtain ⟨r, s, _, _, hr, hs, hne, _⟩ := h.plural
    exact hne (hr.trans hs.symm)
  · intro _ _ _ X act O a f hA hF hSel hEx hCl hO
    exact (TruthCore.Results.Explanation.ExplanatorySymmetry.core).2.1 _ _ _ X (· = act) O a f
      (fun r v hr hv => by rw [hr]; exact hA v hv) hF hSel hEx hCl hO
  · obtain ⟨hM, _, hN, hC, h0, h1, _⟩ :=
      (TruthCore.Results.Explanation.ExplanatorySymmetry.comparison).2.2.2.1
    exact ⟨hM, hN, hC, h0, h1⟩
  -- a condition
  · intro _ _ _ A a act s c hAct hCond hs ⟨_, v, hv, hc⟩
    exact ⟨hs, v, hv, fun hsv => hc (hCond v hv (hAct v hv) hsv)⟩
  · intro _ _ _ A a S s hC hR hF hN
    exact TruthCore.Results.Explanation.ExplanatoryAdequacy.core_necessitate hR hC hF hN
  · obtain ⟨_, _, _, ⟨hb, hc, _⟩, ⟨hcc, hct, hcf, _⟩, ⟨hgc, hgt, hgf, _⟩, _⟩ :=
      TruthCore.Results.Explanation.ExplanatoryAdequacy.core
    refine ⟨⟨hb, hc⟩, ⟨hcc, hct, hcf⟩, ⟨hgc, hgt, hgf, ?_⟩, ?_⟩
    · intro h
      have hx := h (.source true) .target OneSource.target hgt
        (GroundReason.toTarget true (Or.inl rfl)) 1 trivial (Or.inl rfl)
      cases hx
    · intro _ _ _ A a act c hC
      exact ⟨c, fun _ _ _ h => h, hC⟩

/-! ## Branch costs -/

theorem relocated_act_false : ¬ relocated.holds 1 (.source false) := by
  rintro (h | h)
  · cases h
  · exact absurd h (by decide)

theorem relocated_target_false : ¬ relocated.holds 2 .target := by
  rintro (h | h) <;> exact absurd h (by decide)

theorem relocated_target_contingent : Contingent relocated 0 .target :=
  ⟨Or.inl rfl, 2, trivial, relocated_target_false⟩

theorem relocated_act_contingent : Contingent relocated 0 (.source false) :=
  ⟨Or.inr rfl, 1, trivial, relocated_act_false⟩

theorem relocated_source_not_contingent : ¬ Contingent relocated 0 (.source true) := by
  rintro ⟨_, _, _, h⟩
  exact h (Or.inl rfl)

theorem relocated_closed : ReasonClosed relocated 0 RelocatedAccount .target where
  explanandum := .target
  truthful := by
    intro f hf
    cases hf with
    | target => exact Or.inl rfl
    | act => exact Or.inr rfl
    | source => exact Or.inl rfl
  closed := by
    intro r f _ he
    cases he with
    | toAct => exact .source
    | toEffect => exact .act
  covered := by
    intro f hf hc
    cases hf with
    | target => exact ⟨_, .toEffect⟩
    | act => exact ⟨_, .toAct⟩
    | source => exact absurd hc relocated_source_not_contingent
  nonCopy := by
    intro r f _ he _ h
    cases he with
    | toAct =>
      exact relocated_act_false ((h 1 trivial).1 (Or.inl rfl))
    | toEffect =>
      exact relocated_act_false ((h 1 trivial).2 (Or.inr rfl))

theorem relocated_founded : Founded relocated 0 RelocatedAccount := by
  have hact : Acc (ContingentReason relocated 0 RelocatedAccount) (.source false) :=
    ⟨_, fun r ⟨_, _, he, hcr, _⟩ => by
      cases he
      exact absurd hcr relocated_source_not_contingent⟩
  refine ⟨fun f => ⟨f, fun r hr => ?_⟩⟩
  obtain ⟨_, _, he, hcr, _⟩ := hr
  cases he with
  | toAct => exact absurd hcr relocated_source_not_contingent
  | toEffect => exact hact

theorem necessitarian_all : AllReasonsNecessitate necessitarian 0 OneSource :=
  fun _ f _ hc => absurd hc (TruthCore.Results.Explanation.ExplanatoryAdequacy.necessity_not_contingent f)

theorem branchCosts : BranchCosts := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ _ A a r f hN hS ⟨_, v, hv, hf⟩
    exact hf (hS v hv (hN v hv))
  · intro _ _ _ A a S x hC hR hF
    obtain ⟨hv, hn, hc, _⟩ := TruthCore.Results.Explanation.ExplanatoryAdequacy.core
    exact ⟨fun h => hn _ _ _ _ _ _ _ hR hC hF h, fun h => hc _ _ _ _ _ _ _ hR hC hF h,
      fun h => hv _ _ _ _ _ _ _ hR hC hF h⟩
  · refine ⟨fun _ _ => Or.inl rfl, GroundReason.toTarget true (Or.inl rfl), ?_,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_target_contingent false,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_closed,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_founded,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_no_contrast _ OneSource.target⟩
    intro h
    cases h 1 trivial (Or.inl rfl)
  · refine ⟨?_, .toEffect, ?_, relocated_target_contingent, ?_, relocated_closed, relocated_founded,
      fun _ _ => Or.inl rfl, .toAct, ?_, ?_, ?_, ?_⟩
    · exact fun h => relocated_act_false (h 1 trivial)
    · intro v _ h
      rcases h with h | h
      · cases h
      · subst h
        exact Or.inl rfl
    · intro v _ hv h
      rcases h with h | h
      · cases h
      · subst h
        exact hv (Or.inl rfl)
    · exact fun h => relocated_act_false (h 1 trivial (Or.inl rfl))
    · exact relocated_act_false
    · intro r he
      cases he
      exact Or.inl rfl
    · intro h
      obtain ⟨r, _, he, hr⟩ := h _ .act relocated_act_contingent 1 trivial relocated_act_false
      cases he
      exact hr (Or.inl rfl)
  · refine ⟨fun _ _ => rfl, .step 0, fun _ _ _ => trivial,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.necessity_not_contingent,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.necessity_closed,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.necessity_founded,
      necessitarian_all, ?_⟩
    intro f _ hc
    exact absurd hc (TruthCore.Results.Explanation.ExplanatoryAdequacy.necessity_not_contingent f)

end TruthCore.Results.Modal.SimplicityCollapse
