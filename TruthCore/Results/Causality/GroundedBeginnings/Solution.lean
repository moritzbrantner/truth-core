module

public import TruthCore.Causality.GroundedBeginnings
public import TruthCore.Results.Causality.InertEmptiness.Solution
public import TruthCore.Results.Causality.BegunComingToBe.Solution

@[expose] public section

namespace TruthCore.Results.Causality.GroundedBeginnings
open TruthCore.Causality.GroundedBeginnings
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty ConcreteEmptyAt)
open TruthCore.Modal.TemporalHistory (History)

/-- Traced "from nothing, nothing comes" from three principles about grounds.
Fix a history `v` and an earlier moment `s`, and walk down the grounds of a
concrete thing present after `s` by well-founded induction: a thing present at
`s` ends the chain; a thing absent at `s` has begun, so it has a concrete
ground, which is present at `s` (ending the chain) or at some moment after `s`
(where the induction hypothesis applies). -/
theorem nothingFromNothing {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hBegin : BeginningsGrounded h Concrete grounds)
    (hNotCeased : GroundsNotCeasedBeforeAbsence h Concrete grounds)
    (hWF : PresentGroundingWellFounded h Concrete grounds) :
    NothingFromNothing h Concrete grounds := by
  intro v x s t hx hst hxt
  have key : ∀ x, Concrete x → ∀ t, s < t → h.IsAt v x t →
      ∃ y, Concrete y ∧ h.IsAt v y s ∧ Relation.ReflTransGen (grounds v) y x := by
    intro x
    refine WellFounded.induction (C := fun x => Concrete x → ∀ t, s < t → h.IsAt v x t →
      ∃ y, Concrete y ∧ h.IsAt v y s ∧ Relation.ReflTransGen (grounds v) y x) (hWF v) x ?_
    intro x ih hx t hst hxt
    by_cases hxs : h.IsAt v x s
    · exact ⟨x, hx, hxs, Relation.ReflTransGen.refl⟩
    · obtain ⟨g, hg, hgx⟩ := hBegin v x s t hx hst hxs hxt
      rcases hNotCeased v x g s t hx hst hxs hxt hgx with hgs | ⟨u, hsu, hgu⟩
      · exact ⟨g, hg, hgs, Relation.ReflTransGen.single hgx⟩
      · obtain ⟨y, hy, hys, hyg⟩ :=
          ih g ⟨⟨hg, u, hgu⟩, ⟨hx, t, hxt⟩, hgx⟩ hg u hsu hgu
        exact ⟨y, hy, hys, hyg.tail hgx⟩
  exact key x hx t hst hxt

/-- The traced form strengthens inert emptiness (premise A2): it puts a
concrete thing at every moment earlier than a populated one. -/
theorem inertOfNothingFromNothing {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hTraced : NothingFromNothing h Concrete grounds) :
    EmptinessStaysEmpty h Concrete := by
  intro v s t hst hEmpty x hx hxt
  obtain ⟨y, hy, hys, _⟩ := hTraced v x s t hx hst hxt
  exact hEmpty y hy hys

/-- Inert emptiness (premise A2) from the three grounding principles, through
the traced form. -/
theorem inertOfGroundedBeginnings {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hBegin : BeginningsGrounded h Concrete grounds)
    (hNotCeased : GroundsNotCeasedBeforeAbsence h Concrete grounds)
    (hWF : PresentGroundingWellFounded h Concrete grounds) :
    EmptinessStaysEmpty h Concrete :=
  inertOfNothingFromNothing h Concrete grounds
    (nothingFromNothing h Concrete grounds hBegin hNotCeased hWF)

/-- A relation on `Bool` that only ever relates `false` to `true` is well-founded. -/
theorem wfFalseTrue {R : Bool → Bool → Prop}
    (hR : ∀ y x, R y x → y = false ∧ x = true) : WellFounded R := by
  have hf : Acc R false := ⟨_, fun y hy => absurd (hR y false hy).2 (by decide)⟩
  refine ⟨fun x => ⟨_, fun y hy => ?_⟩⟩
  rw [(hR y x hy).1]
  exact hf

/-- A relation whose last conjunct is `False` is well-founded. -/
theorem wfEmpty {B : Type} {P Q : B → Prop} :
    WellFounded fun y x : B => P y ∧ Q x ∧ False :=
  ⟨fun a => ⟨a, fun _ hy => hy.2.2.elim⟩⟩

open TruthCore.Causality.InertEmptiness.Control (exNihilo initialState rooted all)
open TruthCore.Causality.BegunComingToBe.Control (zeno predecessorGrounds)

/-- Omission, strictness, no-re-import and nonvacuity controls. Facts about
`exNihilo`, `initialState`, `rooted` and `zeno` already checked in
`InertEmptiness.controls` and `BegunComingToBe.controls` are reused. -/
theorem controls : Control.Certificate := by
  have hIE := TruthCore.Results.Causality.InertEmptiness.controls
  have hBC := TruthCore.Results.Causality.BegunComingToBe.controls
  refine ⟨⟨?_, ?_, ?_, hIE.2.1.2.2.2.1⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, hBC.2.2.2.2.2.1⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨hIE.2.2.2.2.2.1, ?_⟩,
    ⟨?_, ?_, ?_, hIE.2.2.2.2.1, hIE.2.2.2.2.2.2.1, hIE.2.2.2.2.2.2.2.2⟩⟩
  -- (1) exNihilo without grounds
  · intro _ _ _ _ _ _ _ _ _ hg; exact hg.elim
  · intro _; exact wfEmpty
  · intro hBegin
    obtain ⟨_, _, hg⟩ := hBegin true () 0 1 trivial Nat.zero_lt_one
      (fun hp => absurd hp.2 (by decide)) ⟨rfl, rfl⟩
    exact hg
  -- (2) ceased
  · intro v x s t _ hst hxs hxt
    refine ⟨false, trivial, rfl, ?_⟩
    rcases hxt with ⟨hv, ⟨rfl, rfl⟩ | ⟨rfl, _⟩⟩
    · exact absurd hst (Nat.not_lt_zero s)
    · rfl
  · intro _; exact wfFalseTrue fun _ _ hr => hr.2.2
  · intro hNot
    rcases hNot true true false 1 2 trivial (by decide) (fun hp => by
        rcases hp.2 with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Bool.noConfusion h1
        · exact absurd h2 (by decide)) ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩ ⟨rfl, rfl⟩
      with hp | ⟨u, hu, hp⟩
    · rcases hp.2 with ⟨_, h1⟩ | ⟨h2, _⟩
      · exact absurd h1 (by decide)
      · exact Bool.noConfusion h2
    · rcases hp.2 with ⟨_, h1⟩ | ⟨h2, _⟩
      · subst h1; exact absurd hu (by decide)
      · exact Bool.noConfusion h2
  · intro hInert
    refine hInert true 1 2 (by decide) ?_ true trivial ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
    intro x _ hp
    rcases hp.2 with ⟨_, h1⟩ | ⟨_, h2⟩
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)
  -- (3) zeno with predecessor grounds
  · intro v x s t _ _ _ hxt
    exact ⟨x - 1, trivial, hxt.1, rfl⟩
  · intro v x y s t _ hst hxs hxt hg
    obtain ⟨hv, rfl⟩ := hg
    refine Or.inr ⟨t, hst, hv, ?_⟩
    exact le_trans (WithBot.coe_le_coe.mpr (by omega)) hxt.2
  · intro hWF
    obtain ⟨m, _, hm⟩ := (hWF true).has_min Set.univ ⟨0, trivial⟩
    exact hm (m - 1) trivial
      ⟨⟨trivial, _, rfl, le_refl _⟩, ⟨trivial, _, rfl, le_refl _⟩, rfl, rfl⟩
  -- (4) initialState without grounds
  · intro v x s t _ _ hxs hxt
    exact absurd hxt hxs
  · intro _ _ _ _ _ _ _ _ _ hg; exact hg.elim
  · intro _; exact wfEmpty
  · intro v x s t hx _ hxt
    exact ⟨x, hx, hxt, Relation.ReflTransGen.refl⟩
  · rintro v ⟨_, _, _, hNec⟩
    exact Bool.false_ne_true (hNec false trivial)
  -- (5) strictness: rooted without grounds
  · intro hTraced
    obtain ⟨y, _, hys, hyx⟩ :=
      hTraced true true 0 1 trivial Nat.zero_lt_one (Or.inr ⟨rfl, rfl⟩)
    rcases Relation.ReflTransGen.cases_tail hyx with rfl | ⟨_, _, hg⟩
    · rcases hys with h1 | h2
      · exact Bool.noConfusion h1
      · exact absurd h2.2 (by decide)
    · exact hg
  -- (6) rooted with `false` grounding `true`
  · intro v x s t _ _ hxs hxt
    refine ⟨false, trivial, rfl, ?_⟩
    cases x
    · exact absurd (Or.inl rfl) hxs
    · rfl
  · intro v x y s t _ _ _ _ hg
    obtain ⟨rfl, _⟩ := hg
    exact Or.inl (Or.inl rfl)
  · intro _; exact wfFalseTrue fun _ _ hr => hr.2.2

end TruthCore.Results.Causality.GroundedBeginnings
