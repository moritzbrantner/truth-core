module

public import TruthCore.Causality.SustainingCausation

@[expose] public section

namespace TruthCore.Results.Causality.SustainingCausation
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.GroundedBeginnings (BeginningsHaveLastingGround)
open TruthCore.Causality.DeiFiliusAttributeField (Primitives)
open TruthCore.Causality.DeiFiliusImmenseIncomprehensible
  (IsImmenseAsInfiniteCauseOfAll InfiniteCauseOfAllIsImmense)
open TruthCore.Modal.TemporalHistory (History)

/-- A sustaining cause of a thing that has a first moment of presence is an
originating cause of it. Helper lemma relating the two senses; not registered. -/
theorem originatesOfSustains {W B T : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (v : W) (c x : B) (b : T) (hb : TruthCore.Modal.TemporalHistory.BeginsAt h v x b)
    (hs : SustainsBeing h G v c x) : OriginatesBeing h G v c x :=
  ⟨b, hb, hs.2 b hb.1⟩

/-- From the contact principle: whatever sustains every other thing is present,
by giving it being, to every other thing at every moment at which that thing is
present. The sustainer gives `x` being at each such `t`, and a giver is present
when it gives. -/
theorem sustainerOfAllIsPresentToAll {W B T : Type} (h : History W B T)
    (G : BeingGiving W B T) (hContact : GiverPresentWhenGiving h G) :
    SustainerOfAllIsPresentToAll h G := by
  intro v g hAll x t hxg hxt
  have hGive := (hAll x hxg ⟨t, hxt⟩).2 t hxt
  exact ⟨hContact v g x t hGive, hGive⟩

/-- The presence step of the immensity sense bridge, derived: whatever is
IMMENSE_2 is, in every history, present by giving being to every other thing
whenever it is. Its creator conjunct makes it a cause of the being of every
other thing in act as to being; what is present is in act as to being; the
sustaining reading turns each such cause into a sustainer; and the contact
principle puts the sustainer at each moment at which its effect is. The
infinity conjunct is not used. -/
theorem immense2PresentToAll {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop)
    (hSustaining : CausingBeingIsSustaining h G CausesIn esse)
    (hInAct : PresentIsInActAsToBeing h InAct esse)
    (hContact : GiverPresentWhenGiving h G) :
    Immense2PresentToAll h G InAct CausesIn esse Infinite := by
  intro v g hg
  refine sustainerOfAllIsPresentToAll h G hContact v g ?_
  intro x hxg hx
  obtain ⟨t, hxt⟩ := hx
  exact hSustaining v g x (hg.2 x hxg (hInAct v x t hxt)) ⟨t, hxt⟩

/-- The immensity sense bridge IMMENSE_2 → IMMENSE_1 (`8bf775e9`) from the typed
presence step and the narrowed bridge that carries the rest (place,
containment, measure, the other modes of presence, immediacy). -/
theorem immenseSenseBridgeOfSustainingPresence {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop) (D : Primitives B)
    (hSustaining : CausingBeingIsSustaining h G CausesIn esse)
    (hInAct : PresentIsInActAsToBeing h InAct esse)
    (hContact : GiverPresentWhenGiving h G)
    (hNarrow : PresentInfiniteCauseOfAllIsImmense h G InAct CausesIn esse Infinite D) :
    InfiniteCauseOfAllIsImmense InAct CausesIn esse Infinite D := by
  intro g hg
  exact hNarrow g hg fun v =>
    immense2PresentToAll h G InAct CausesIn esse Infinite hSustaining hInAct hContact v g hg

/-- Strength order: the immensity sense bridge entails its narrowed form, whose
antecedent adds presence to all. -/
theorem narrowedOfImmenseSenseBridge {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop) (D : Primitives B)
    (hBridge : InfiniteCauseOfAllIsImmense InAct CausesIn esse Infinite D) :
    PresentInfiniteCauseOfAllIsImmense h G InAct CausesIn esse Infinite D :=
  fun g hg _ => hBridge g hg

/-- Lasting ground (A2ab) from sustaining causes. A concrete thing absent at `s`
and present at `t > s` has a concrete sustaining cause; it gives the thing being
at `t`, so by the contact principle it is present at `t`, which is after `s`;
and it is a ground. -/
theorem lastingGroundOfSustainingCauses {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : BeingGiving W B T) (grounds : W → B → B → Prop)
    (hCause : BeginningsHaveSustainingCause h Concrete G)
    (hGround : SustainersAreGrounds h G grounds)
    (hContact : GiverPresentWhenGiving h G) :
    BeginningsHaveLastingGround h Concrete grounds := by
  intro v x s t hx hst hxs hxt
  obtain ⟨g, hg, hSus⟩ := hCause v x s t hx hst hxs hxt
  exact ⟨g, hg, hGround v g x hSus, Or.inr ⟨t, hst, hContact v g x t (hSus.2 t hxt)⟩⟩

/-- Lasting ground (A2ab) from originating causes, given that any two moments
are comparable and concrete presence has no gaps. A concrete thing absent at `s`
and present at `t > s` has a concrete originating cause, which gives it being at
a first moment `b` of its presence and so (contact) is present at `b`. The moment
`b` is not `s` (the thing is absent at `s`) and not before `s` (it would then be
present at `b` and `t` and absent between them), so it is after `s`. -/
theorem lastingGroundOfOriginatingCauses {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : BeingGiving W B T) (grounds : W → B → B → Prop)
    (hCause : BeginningsHaveOriginatingCause h Concrete G)
    (hGround : OriginatorsAreGrounds h G grounds)
    (hContact : GiverPresentWhenGiving h G)
    (hConvex : ConcretePresenceConvex h Concrete)
    (hTri : TimesTrichotomous T) :
    BeginningsHaveLastingGround h Concrete grounds := by
  intro v x s t hx hst hxs hxt
  obtain ⟨g, hg, hOrig⟩ := hCause v x s t hx hst hxs hxt
  obtain ⟨b, hb, hGive⟩ := hOrig
  refine ⟨g, hg, hGround v g x ⟨b, hb, hGive⟩, Or.inr ⟨b, ?_, hContact v g x b hGive⟩⟩
  rcases hTri b s with hbs | rfl | hsb
  · exact absurd (hConvex v x b s t hx hbs hst hb.1 hxt) hxs
  · exact absurd hb.1 hxs
  · exact hsb

open TruthCore.Causality.SustainingCausation.Control

/-- Omission, rival-reading and nonvacuity controls (`Control.Certificate`). -/
theorem controls : Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- (1) inertia
  · rintro v c x ⟨rfl, rfl⟩ _
    refine ⟨1, ⟨Or.inr ⟨rfl, le_refl 1⟩, ?_⟩, rfl, rfl, rfl⟩
    intro s hs hp
    rcases hp with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Bool.noConfusion h1
    · omega
  · intro hS
    have := (hS () true false ⟨rfl, rfl⟩ ⟨1, Or.inr ⟨rfl, le_refl 1⟩⟩).2 2
      (Or.inr ⟨rfl, by decide⟩)
    exact absurd this.2.2 (by decide)
  · intro _ _ _ _; trivial
  · rintro v c x t ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, le_refl 1⟩
  · refine ⟨rfl, ?_⟩
    intro x hx _
    cases x
    · exact ⟨rfl, rfl⟩
    · exact absurd rfl hx
  · intro hP
    have := (hP () true ⟨rfl, fun x hx _ => by cases x <;> simp_all [trueCausesFalse]⟩
      false 2 (by decide) (Or.inr ⟨rfl, by decide⟩)).1
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact Bool.noConfusion h
  · intro v x s t _ hst hxs hxt
    rcases hxt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩
    · exact absurd (Or.inl ⟨rfl, by omega⟩) hxs
    · refine ⟨true, trivial, 1, ⟨Or.inr ⟨rfl, le_refl 1⟩, ?_⟩, rfl, rfl, rfl⟩
      intro u hu hp
      rcases hp with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Bool.noConfusion h1
      · omega
  · rintro v g x ⟨b, _, hg, hx, _⟩
    exact ⟨hg, hx⟩
  · intro v x a s t _ has hst hxa hxt
    rcases hxa with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rcases hxt with ⟨_, ht⟩ | ⟨h, _⟩
      · exact Or.inl ⟨rfl, by omega⟩
      · exact Bool.noConfusion h
    · exact Or.inr ⟨rfl, by omega⟩
  · intro v x s t _ hst hxs hxt
    rcases hxt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩
    · exact absurd (Or.inl ⟨rfl, by omega⟩) hxs
    · refine ⟨true, trivial, ⟨rfl, rfl⟩, ?_⟩
      have hs : s = 0 := by
        by_contra hne
        exact hxs (Or.inr ⟨rfl, by omega⟩)
      subst hs
      exact Or.inl (Or.inl ⟨rfl, by decide⟩)
  · intro hS
    obtain ⟨g, _, hSus⟩ := hS () false 0 1 trivial (by decide)
      (fun hp => by rcases hp with ⟨h, _⟩ | ⟨_, h⟩ <;> simp_all) (Or.inr ⟨rfl, le_refl 1⟩)
    have := (hSus.2 2 (Or.inr ⟨rfl, by decide⟩)).2.2
    exact absurd this (by decide)
  -- (2) absentGiver
  · rintro v c x ⟨rfl, rfl⟩ _
    exact ⟨⟨1, rfl, le_refl 1⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  · intro _ _ _ _; trivial
  · intro hC
    have := hC () true false 0 ⟨rfl, rfl⟩
    exact Bool.noConfusion this.1
  · intro hP
    have := (hP () true ⟨rfl, fun x hx _ => by cases x <;> simp_all [trueCausesFalse]⟩
      false 1 (by decide) ⟨rfl, le_refl 1⟩).1
    exact Bool.noConfusion this.1
  · intro v x s t _ _ _ hxt
    obtain ⟨rfl, _⟩ := hxt
    exact ⟨true, trivial, ⟨⟨t, rfl, by assumption⟩, fun _ _ => ⟨rfl, rfl⟩⟩⟩
  · rintro v g x ⟨⟨t, hxt⟩, hAll⟩
    exact hAll t hxt
  · intro hL
    obtain ⟨y, _, hy, hp⟩ := hL () false 0 1 trivial (by decide)
      (fun hp => by simp_all [absentGiver]) ⟨rfl, le_refl 1⟩
    obtain ⟨rfl, _⟩ := hy
    rcases hp with hp | ⟨_, _, hp⟩
    · exact Bool.noConfusion hp.1
    · exact Bool.noConfusion hp.1
  -- (3) sustained, no giving
  · intro hS
    exact (hS () true false ⟨rfl, rfl⟩ ⟨1, Or.inr ⟨rfl, le_refl 1⟩⟩).2 1
      (Or.inr ⟨rfl, le_refl 1⟩)
  · intro _ _ _ _; trivial
  · intro _ _ _ _ h; exact h.elim
  · intro hP
    exact (hP () true ⟨rfl, fun x hx _ => by cases x <;> simp_all [trueCausesFalse]⟩
      false 1 (by decide) (Or.inr ⟨rfl, le_refl 1⟩)).2
  · rintro v g x ⟨⟨t, hxt⟩, hAll⟩
    exact hAll t hxt
  · intro hS
    obtain ⟨_, _, hSus⟩ := hS () false 0 1 trivial (by decide)
      (fun hp => by rcases hp with h | ⟨_, h⟩ <;> simp_all) (Or.inr ⟨rfl, le_refl 1⟩)
    exact hSus.2 1 (Or.inr ⟨rfl, le_refl 1⟩)
  · intro hL
    obtain ⟨_, _, hy, _⟩ := hL () false 0 1 trivial (by decide)
      (fun hp => by rcases hp with h | ⟨_, h⟩ <;> simp_all) (Or.inr ⟨rfl, le_refl 1⟩)
    exact hy
  -- (4) sustained, nothing in act
  · intro _ _ _ h; exact h.elim
  · intro hP; exact hP () true 0 (Or.inl rfl)
  · intro _ _ _ _ h; exact h.elim
  · exact ⟨rfl, fun _ _ h => h.elim⟩
  · intro hP
    exact (hP () true ⟨rfl, fun _ _ h => h.elim⟩ false 1 (by decide)
      (Or.inr ⟨rfl, le_refl 1⟩)).2
  -- (5) sustained, sustainers not grounds
  · intro v x s t _ _ hxs hxt
    rcases hxt with rfl | ⟨rfl, ht⟩
    · exact absurd (Or.inl rfl) hxs
    · refine ⟨true, trivial, ⟨⟨t, Or.inr ⟨rfl, ht⟩⟩, fun u hu => ?_⟩⟩
      rcases hu with h | ⟨_, hu⟩
      · exact Bool.noConfusion h
      · exact ⟨rfl, rfl, hu⟩
  · rintro v c x t ⟨rfl, _, _⟩
    exact Or.inl rfl
  · intro hG
    exact hG () true false ⟨⟨1, Or.inr ⟨rfl, le_refl 1⟩⟩, fun u hu => by
      rcases hu with h | ⟨_, hu⟩
      · exact Bool.noConfusion h
      · exact ⟨rfl, rfl, hu⟩⟩
  · intro hL
    obtain ⟨_, _, hy, _⟩ := hL () false 0 1 trivial (by decide)
      (fun hp => by rcases hp with h | ⟨_, h⟩ <;> simp_all) (Or.inr ⟨rfl, le_refl 1⟩)
    exact hy
  -- (6) intermittent
  · intro v x s t _ hst hxs hxt
    rcases hxt with ⟨rfl, rfl⟩ | ⟨rfl, ht⟩
    · exact absurd hst (Nat.not_lt_zero s)
    · refine ⟨true, trivial, 0, ⟨Or.inr ⟨rfl, Or.inl rfl⟩, fun u hu => absurd hu
        (Nat.not_lt_zero u)⟩, rfl, rfl, rfl⟩
  · rintro v g x ⟨b, _, hg, hx, _⟩
    exact ⟨hg, hx⟩
  · rintro v c x t ⟨rfl, _, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩
  · exact fun a b => lt_trichotomy a b
  · intro hC
    have := hC () false 0 1 2 trivial (by decide) (by decide)
      (Or.inr ⟨rfl, Or.inl rfl⟩) (Or.inr ⟨rfl, Or.inr rfl⟩)
    rcases this with ⟨h, _⟩ | ⟨_, h⟩
    · exact Bool.noConfusion h
    · omega
  · intro hL
    obtain ⟨y, _, hy, hp⟩ := hL () false 1 2 trivial (by decide)
      (fun hp => by rcases hp with ⟨h, _⟩ | ⟨_, h⟩ <;> simp_all)
      (Or.inr ⟨rfl, Or.inr rfl⟩)
    obtain ⟨rfl, _⟩ := hy
    rcases hp with hp | ⟨u, hu, hp⟩
    · rcases hp with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact Bool.noConfusion h
    · rcases hp with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact Bool.noConfusion h
  -- (7) sustained, with giving: nonvacuity
  · rintro v c x ⟨rfl, rfl⟩ _
    refine ⟨⟨1, Or.inr ⟨rfl, le_refl 1⟩⟩, fun u hu => ?_⟩
    rcases hu with h | ⟨_, hu⟩
    · exact Bool.noConfusion h
    · exact ⟨rfl, rfl, hu⟩
  · intro _ _ _ _; trivial
  · rintro v c x t ⟨rfl, _, _⟩
    exact Or.inl rfl
  · refine ⟨rfl, ?_⟩
    intro x hx _
    cases x
    · exact ⟨rfl, rfl⟩
    · exact absurd rfl hx
  · rintro v g ⟨hg, _⟩ x t hxg hxt
    subst hg
    rcases hxt with rfl | ⟨rfl, ht⟩
    · exact absurd rfl hxg
    · exact ⟨Or.inl rfl, rfl, rfl, ht⟩
  · intro v x s t _ _ hxs hxt
    rcases hxt with rfl | ⟨rfl, ht⟩
    · exact absurd (Or.inl rfl) hxs
    · refine ⟨true, trivial, ⟨⟨t, Or.inr ⟨rfl, ht⟩⟩, fun u hu => ?_⟩⟩
      rcases hu with h | ⟨_, hu⟩
      · exact Bool.noConfusion h
      · exact ⟨rfl, rfl, hu⟩
  · rintro v g x ⟨⟨t, hxt⟩, hAll⟩
    obtain ⟨hg, hx, _⟩ := hAll t hxt
    exact ⟨hg, hx⟩
  · intro v x s t _ hst hxs hxt
    rcases hxt with rfl | ⟨rfl, ht⟩
    · exact absurd (Or.inl rfl) hxs
    · refine ⟨true, trivial, 1, ⟨Or.inr ⟨rfl, le_refl 1⟩, fun u hu hp => ?_⟩, rfl, rfl,
        le_refl 1⟩
      rcases hp with h | ⟨_, h⟩
      · exact Bool.noConfusion h
      · omega
  · rintro v g x ⟨b, _, hg, hx, _⟩
    exact ⟨hg, hx⟩
  · intro v x a s t _ has hst hxa hxt
    rcases hxa with rfl | ⟨rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, by omega⟩
  · exact fun a b => lt_trichotomy a b
  · intro v x s t _ hst hxs hxt
    rcases hxt with rfl | ⟨rfl, ht⟩
    · exact absurd (Or.inl rfl) hxs
    · exact ⟨true, trivial, ⟨rfl, rfl⟩, Or.inr ⟨t, hst, Or.inl rfl⟩⟩

end TruthCore.Results.Causality.SustainingCausation
