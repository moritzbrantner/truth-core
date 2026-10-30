import TruthCore.Modal.WorldwiseExplanation

/-! #465, a fixed roster of rigid reason tokens with varying actual membership.
The extra domain predicate concerns tokens, not their external causal bearers.
No attribution to a historical author or metaphysical sufficiency is claimed.
-/
namespace TruthCore.Modal.ActualReasonWitness
open TruthCore.Explanation.ExistencePSR
open TruthCore.Modal.WorldwiseExplanation
variable {W B : Type}

/-- A reason both belongs to the supplied actual token domain and explains the
selected existence fact at this world. Membership is not implicit in Reason. -/
def Admitted (m : Model W B) (domain : W → Reason B → Prop)
    (x : B) (w : W) (r : Reason B) : Prop :=
  domain w r ∧ m.explains w r (.fact x)

/-- Same actual token at all worlds of this individual's existence. It makes
no explanation claim at a world where the individual does not exist. -/
def ActualStable (m : Model W B) (domain : W → Reason B → Prop) (x : B) : Prop :=
  ∃ r, ∀ w, m.ontic.ExistsAt w x → Admitted m domain x w r

/-- Anchor has exactly one admitted reason; every world of existence shares
some admitted reason with that anchor. The shared witnesses may initially vary.
This is an explicit open bridge, not a consequence of local PSR. -/
def AnchorOverlap (m : Model W B) (domain : W → Reason B → Prop) (x : B) : Prop :=
  ∃ a, m.ontic.ExistsAt a x ∧
    (∃ r, Admitted m domain x a r ∧
      ∀ s, Admitted m domain x a s → s = r) ∧
    (∀ v, m.ontic.ExistsAt v x →
      ∃ s, Admitted m domain x a s ∧ Admitted m domain x v s)

/-- Anchor uniqueness turns varying overlap witnesses into the same token.
No full invariance of all explanatory tokens is required. -/
theorem anchorOverlap_implies_actualStable (m : Model W B)
    (domain : W → Reason B → Prop) (x : B)
    (h : AnchorOverlap m domain x) : ActualStable m domain x := by
  obtain ⟨a, _, ⟨r, _, unique⟩, overlap⟩ := h
  refine ⟨r, ?_⟩
  intro v hv
  obtain ⟨s, hs, hsv⟩ := overlap v hv
  have heq := unique s hs
  subst s
  exact hsv

theorem actualStable_implies_stable (m : Model W B)
    (domain : W → Reason B → Prop) (x : B)
    (h : ActualStable m domain x) : StableExplanation m x := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun w hw => (hr w hw).2⟩

/-- The old alternating model admits its sole local token as actual. Thus even
actual local explanations plus a necessary bearer do not repair the shift. -/
def alternatingDomain (w : Bool) (r : Reason Bool) : Prop :=
  r = .circumstance w

theorem alternating_actual_local :
    ∀ w x, WorldwiseExplanation.alternating.ontic.ExistsAt w x →
      ∃ r, Admitted WorldwiseExplanation.alternating alternatingDomain x w r := by
  intro w x hx
  exact ⟨.circumstance w, rfl, hx, rfl⟩

theorem alternating_not_actualStable :
    ¬ ActualStable WorldwiseExplanation.alternating alternatingDomain false := by
  intro h
  exact alternatingNotStable (actualStable_implies_stable _ _ _ h)

/-- Two-world positive control: token intrinsic false explains at both worlds;
an additional circumstance token explains only at true. It is deliberately
not invariant, although the anchor-overlap bridge succeeds. -/
def overlapModel : Model Bool Bool where
  ontic := WorldwiseExplanation.alternating.ontic
  explains := fun w r f => match f with
    | .fact x => x = false ∧
        (r = .intrinsic false ∨ (w = true ∧ r = .circumstance true))

def overlapDomain (w : Bool) (r : Reason Bool) : Prop :=
  r = .intrinsic false ∨ (w = true ∧ r = .circumstance true)

theorem overlap_sound : Sound overlapModel := by
  intro _ _ _ h
  exact h.1

theorem overlap_anchor : AnchorOverlap overlapModel overlapDomain false := by
  refine ⟨false, rfl, ⟨.intrinsic false, ?_, ?_⟩, ?_⟩
  · exact ⟨Or.inl rfl, rfl, Or.inl rfl⟩
  · intro s hs
    rcases hs.1 with hs | ⟨hf, _⟩
    · exact hs
    · cases hf
  · intro v _
    exact ⟨.intrinsic false, ⟨Or.inl rfl, rfl, Or.inl rfl⟩,
      ⟨Or.inl rfl, rfl, Or.inl rfl⟩⟩

theorem overlap_not_invariant : ¬ ReasonInvariant overlapModel false := by
  intro h
  have hf := h true false (.circumstance true)
    ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩ rfl
  rcases hf.2 with hf | ⟨hf, _⟩ <;> cases hf

/-- Closed certificate: conditional bridge and projection, actualist alternating
countermodel, and populated sound positive control failing full invariance.
All domains and individual-existence guards remain explicit. No external cause,
essential sufficiency, circularity prohibition or necessary token is inferred. -/
def Certificate : Prop :=
  (∀ (W B : Type) (m : Model W B) d x,
    AnchorOverlap m d x → ActualStable m d x) ∧
  (∀ (W B : Type) (m : Model W B) d x,
    ActualStable m d x → StableExplanation m x) ∧
  (Sound WorldwiseExplanation.alternating ∧
    (∀ w x, WorldwiseExplanation.alternating.ontic.ExistsAt w x →
      ∃ r, Admitted WorldwiseExplanation.alternating alternatingDomain x w r) ∧
    ¬ ActualStable WorldwiseExplanation.alternating alternatingDomain false) ∧
  (Sound overlapModel ∧ AnchorOverlap overlapModel overlapDomain false ∧
    ActualStable overlapModel overlapDomain false ∧
    ¬ ReasonInvariant overlapModel false)
end TruthCore.Modal.ActualReasonWitness
