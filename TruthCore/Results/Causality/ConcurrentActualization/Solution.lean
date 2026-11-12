module

public import TruthCore.Causality.ConcurrentActualization

@[expose] public section

namespace TruthCore.Results.Causality.ConcurrentActualization

open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Modal.TemporalHistory (History)

/-- The weak sustaining reading from concurrent actualization. Let `c`, distinct
from `x`, cause `x`'s being, and let `x` be present at `t`. By the reception
bridge `x`'s esse is received in some principle; by concurrent actualization
something gives `x` being at `t`; by concurrence `c` gives `x` being at `t`. So
`c` gives `x` being at every moment at which `x` is present. -/
theorem sustainingOfConcurrentActualization {W B T P Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (EsseReceivedIn : B → P → Prop)
    (hReceived : CausedEsseIsReceived CausesIn esse EsseReceivedIn)
    (hActualized : ConcurrentlyActualized h G EsseReceivedIn)
    (hConcur : CausesOfBeingConcur G CausesIn esse) :
    CausingAnothersBeingIsSustaining h G CausesIn esse := by
  intro v c x hcx hC hx
  refine ⟨hx, fun t ht => ?_⟩
  obtain ⟨z, hz⟩ := hReceived c x hcx hC
  obtain ⟨g, hg⟩ := hActualized v x t z hz ht
  exact hConcur v c g x t hcx hC hg

/-- Strength order: the strong concurrent actualization (a giver distinct from
the thing) entails the weak one. -/
theorem concurrentlyActualizedOfByAnother {W B T P : Type} (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop)
    (hStrong : ConcurrentlyActualizedByAnother h G EsseReceivedIn) :
    ConcurrentlyActualized h G EsseReceivedIn := by
  intro v x t z hz ht
  obtain ⟨g, _, hg⟩ := hStrong v x t z hz ht
  exact ⟨g, hg⟩

/-- Strength order: the sustaining reading `23e04ae5` entails its restriction to
causes distinct from their effect. -/
theorem anothersSustainingOfSustaining {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hSustaining : CausingBeingIsSustaining h G CausesIn esse) :
    CausingAnothersBeingIsSustaining h G CausesIn esse :=
  fun v c x _ hC hx => hSustaining v c x hC hx

/-- The presence step of the immensity sense bridge from the weak sustaining
reading: the creator conjunct of IMMENSE_2 concerns only other beings, so the
restriction to causes distinct from their effect suffices. -/
theorem immense2PresentToAllOfAnothers {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop)
    (hSustaining : CausingAnothersBeingIsSustaining h G CausesIn esse)
    (hInAct : PresentIsInActAsToBeing h InAct esse)
    (hContact : GiverPresentWhenGiving h G) :
    Immense2PresentToAll h G InAct CausesIn esse Infinite := by
  intro v g hg x t hxg hxt
  have hGive := (hSustaining v g x (Ne.symm hxg) (hg.2 x hxg (hInAct v x t hxt)) ⟨t, hxt⟩).2 t hxt
  exact ⟨hContact v g x t hGive, hGive⟩

/-- The immensity sense bridge IMMENSE_2 → IMMENSE_1 (`8bf775e9`) from the weak
sustaining reading, presence-in-act, contact and the narrowed bridge that carries
the rest (place, containment, measure, the other modes of presence,
immediacy). -/
theorem immenseSenseBridgeOfAnothersSustaining {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop) (D : TruthCore.Causality.DeiFiliusAttributeField.Primitives B)
    (hSustaining : CausingAnothersBeingIsSustaining h G CausesIn esse)
    (hInAct : PresentIsInActAsToBeing h InAct esse)
    (hContact : GiverPresentWhenGiving h G)
    (hNarrow : PresentInfiniteCauseOfAllIsImmense h G InAct CausesIn esse Infinite D) :
    TruthCore.Causality.DeiFiliusImmenseIncomprehensible.InfiniteCauseOfAllIsImmense
      InAct CausesIn esse Infinite D := by
  intro g hg
  exact hNarrow g hg fun v =>
    immense2PresentToAllOfAnothers h G InAct CausesIn esse Infinite hSustaining hInAct hContact v g hg

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control

/-- Rival-reading, omission, strictness and nonvacuity controls
(`Control.Certificate`). -/
theorem controls : TruthCore.Causality.ConcurrentActualization.Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- (1) extrinsic inertia
  · rintro c x _ ⟨_, rfl⟩
    exact ⟨(), rfl⟩
  · rintro v c g x t _ ⟨rfl, rfl⟩ ⟨_, _, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · intro _ _ _ _; trivial
  · rintro v c x t ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, le_refl 1⟩
  · intro hA
    obtain ⟨g, _, _, h2⟩ := hA () false 2 () rfl (Or.inr ⟨rfl, by decide⟩)
    exact absurd h2 (by decide)
  · intro hS
    have := (hS () true false (by decide) ⟨rfl, rfl⟩ ⟨1, Or.inr ⟨rfl, le_refl 1⟩⟩).2 2
      (Or.inr ⟨rfl, by decide⟩)
    exact absurd this.2.2 (by decide)
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
  -- (2) intrinsic persistence power
  · rintro c x _ ⟨_, rfl⟩
    exact ⟨(), rfl⟩
  · rintro v x t z rfl hxt
    rcases hxt with ⟨h, _⟩ | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨false, rfl, Or.inr ⟨rfl, ht⟩⟩
  · rintro v c x t ⟨rfl, hct⟩
    rcases hct with ⟨rfl, rfl⟩ | ⟨rfl, ht⟩
    · exact Or.inl ⟨rfl, le_refl 1⟩
    · exact Or.inr ⟨rfl, ht⟩
  · intro hA
    obtain ⟨g, hg, _, hct⟩ := hA () false 2 () rfl (Or.inr ⟨rfl, by decide⟩)
    rcases hct with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact hg h
  · intro hC
    have := hC () true false false 2 (by decide) ⟨rfl, rfl⟩ ⟨rfl, Or.inr ⟨rfl, by decide⟩⟩
    rcases this.2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact Bool.noConfusion h
  · intro hS
    have := (hS () true false (by decide) ⟨rfl, rfl⟩ ⟨1, Or.inr ⟨rfl, le_refl 1⟩⟩).2 2
      (Or.inr ⟨rfl, by decide⟩)
    rcases this.2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact Bool.noConfusion h
  -- (3) relay
  · rintro c x _ ⟨_, rfl⟩
    exact ⟨(), rfl⟩
  · rintro v x t z rfl hxt
    rcases hxt with ⟨h, _⟩ | ⟨_, ht⟩ | h
    · exact absurd h (by decide)
    · rcases Nat.lt_or_ge t 2 with hlt | hge
      · exact ⟨0, by decide, rfl, Or.inl ⟨rfl, by omega⟩⟩
      · exact ⟨2, by decide, rfl, Or.inr ⟨rfl, hge⟩⟩
    · exact absurd h (by decide)
  · rintro v c x t ⟨rfl, hct⟩
    rcases hct with ⟨rfl, rfl⟩ | ⟨rfl, _⟩
    · exact Or.inl ⟨rfl, le_refl 1⟩
    · exact Or.inr (Or.inr rfl)
  · intro hC
    have := hC () 0 2 1 2 (by decide) ⟨rfl, rfl⟩ ⟨rfl, Or.inr ⟨rfl, le_refl 2⟩⟩
    rcases this.2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · intro hS
    have := (hS () 0 1 (by decide) ⟨rfl, rfl⟩ ⟨1, Or.inr (Or.inl ⟨rfl, le_refl 1⟩)⟩).2 2
      (Or.inr (Or.inl ⟨rfl, by decide⟩))
    rcases this.2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  -- (4) no received esse
  · intro hR
    obtain ⟨_, h⟩ := hR true false (by decide) ⟨rfl, rfl⟩
    exact h
  · intro _ _ _ _ h; exact h.elim
  · intro _ _ _ _ h; exact h.elim
  · rintro v c g x t _ ⟨rfl, rfl⟩ ⟨_, _, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · intro hS
    have := (hS () true false (by decide) ⟨rfl, rfl⟩ ⟨1, Or.inr ⟨rfl, le_refl 1⟩⟩).2 2
      (Or.inr ⟨rfl, by decide⟩)
    exact absurd this.2.2 (by decide)
  -- (5) self-causes
  · rintro v c x hcx hC _
    exact absurd hC hcx
  · intro hS
    exact (hS () true true rfl ⟨0, Or.inl rfl⟩).2 0 (Or.inl rfl)
  -- (6) contact and presence-in-act needed
  · rintro v c x _ ⟨rfl, rfl⟩ _
    exact ⟨⟨1, rfl, le_refl 1⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  · intro _ _ _ _; trivial
  · intro hC
    have := hC () true false 0 ⟨rfl, rfl⟩
    exact Bool.noConfusion this.1
  · intro hP
    have := (hP () true ⟨rfl, fun x hx _ => by cases x <;> simp_all [trueCausesFalse]⟩
      false 1 (by decide) ⟨rfl, le_refl 1⟩).1
    exact Bool.noConfusion this.1
  · intro _ _ _ _ h; exact h.elim
  · intro _ _ _ _ h; exact h.elim
  · intro hP; exact hP () true 0 (Or.inl rfl)
  · intro hP
    exact (hP () true ⟨rfl, fun _ _ h => h.elim⟩ false 1 (by decide)
      (Or.inr ⟨rfl, le_refl 1⟩)).2
  -- (7) nonvacuity
  · rintro c x _ ⟨_, rfl⟩
    exact ⟨(), rfl⟩
  · rintro v x t z rfl hxt
    rcases hxt with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, by decide, rfl, rfl, ht⟩
  · rintro v x t z rfl hxt
    rcases hxt with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩
  · rintro v c g x t _ ⟨rfl, rfl⟩ ⟨_, _, ht⟩
    exact ⟨rfl, rfl, ht⟩
  · rintro v c x _ ⟨rfl, rfl⟩ ⟨t, ht⟩
    refine ⟨⟨t, ht⟩, fun u hu => ?_⟩
    rcases hu with h | ⟨_, hu⟩
    · exact Bool.noConfusion h
    · exact ⟨rfl, rfl, hu⟩
  · rintro v c x ⟨rfl, rfl⟩ ⟨t, ht⟩
    refine ⟨⟨t, ht⟩, fun u hu => ?_⟩
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
  · intro v g hg x t hxg hxt
    have hgt : g = true := hg.1
    subst hgt
    cases x
    · rcases hxt with h | ⟨_, ht⟩
      · exact Bool.noConfusion h
      · exact ⟨Or.inl rfl, rfl, rfl, ht⟩
    · exact absurd rfl hxg

end TruthCore.Results.Causality.ConcurrentActualization
