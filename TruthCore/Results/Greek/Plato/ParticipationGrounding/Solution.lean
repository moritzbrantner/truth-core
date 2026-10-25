import TruthCore.Greek.Plato.ParticipationGrounding
namespace TruthCore.Results.Greek.Plato.ParticipationGrounding
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ParticipationGrounding
private instance : NeZero 4 where
  out h := Nat.noConfusion h

universe u v w
variable {Entity : Type u} {Quality : Type v} {Feature : Type w}

/-- Only the assignment changes; all explanatory-sounding predicates are fixed.
Their truth-valued extensions do not constitute an explanatory mechanism. -/
private def model (selected : Fin 4) : Vocabulary (Fin 4) Unit where
  Particular x := x ≠ 0
  Admitted _ := True
  FormOf f _ := f = 0
  Exemplifies x _ := x = 3 ∨ x = selected
  Participates x f := (x = 3 ∨ x = selected) ∧ f = 0
  Independent f := f = 0
  Intelligible f := f = 0
  Unchanging f := f = 0
  Explains _ _ _ := True
  ModelFor _ _ := True
  Imitates _ _ := True
  Like _ _ := True
  Essentially _ _ := True

private def empty : Explanation (Fin 4) Unit Unit where
  Base x _ := x = 3 ∨ x = 1
  Grounds _ _ := False
  Produces _ _ _ := False
  Identifies _ _ _ := False

private def directed : Explanation (Fin 4) Unit Unit where
  Base x _ := x = 3 ∨ x = 1
  Grounds a b := ∃ x, (x = 3 ∨ x = 1) ∧
    a = .base x () ∧ b = .participation x 0
  Produces f x _ := f = 0 ∧ (x = 3 ∨ x = 1)
  Identifies agent x _ := agent = 2 ∧ (x = 3 ∨ x = 1)

private theorem genericModel (selected : Fin 4) (hs0 : selected ≠ 0)
    (hs3 : selected ≠ 3) : Generic (model selected) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨selected, 3, (), hs3, hs0, (by change (3 : Fin 4) ≠ 0; decide +kernel),
      True.intro, Or.inr rfl, Or.inl rfl⟩
  · intro q _
    exact ⟨0, rfl, fun x _ hx => ⟨hx, rfl⟩⟩
  · intro q _ f g hf hg
    exact hf.trans hg.symm
  · intro q _ f x _ _ hp
    exact hp.1
  · intro q _ f x hf hx _ hfx
    exact hx (hfx.symm.trans hf)
  · intro q _ f hf
    exact hf
  · intro q _ x _ hx
    exact ⟨0, rfl, ⟨hx, rfl⟩, True.intro⟩
  · intro q _ x _ _
    exact ⟨0, rfl, True.intro, True.intro⟩
  · intro q _ f hf
    exact ⟨hf, hf⟩
  · intro q _ f _
    exact True.intro
  · intro q f x _ hf _
    exact ⟨fun hx => ⟨hx, hf⟩, fun hp => hp.1⟩

private theorem genericOne : Generic (model 1) :=
  genericModel 1 (by decide +kernel) (by decide +kernel)
private theorem genericTwo : Generic (model 2) :=
  genericModel 2 (by decide +kernel) (by decide +kernel)

/-- Same base facts and generic principles, different participants. No claim
that actual human nature is unchanged between these formal interpretations. -/
theorem assignmentUnderdetermined : AssignmentUnderdetermined := by
  refine ⟨model 1, model 2, empty, genericOne, genericTwo, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro x
    exact Iff.rfl
  all_goals first
    | exact fun _ _ h => h
    | (dsimp only [model, empty] <;> decide +kernel)

/-- The base-to-participation edge cannot reverse: its constructors differ.
This is an explicitly interpreted, noncircular directed relation. -/
theorem groundingIndependent : GroundingIndependent := by
  refine ⟨model 1, directed, empty, genericOne, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  · intro x hx
    exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  · intro x hx hg
    exact ⟨x, hg, rfl, rfl⟩
  · intro a b hab hba
    obtain ⟨x, _, ha, hb⟩ := hab
    obtain ⟨y, _, hb', _⟩ := hba
    cases hb.symm.trans hb'
  · refine ⟨?_, ?_, True.intro, True.intro, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (dsimp only [model, directed, empty] <;> first | exact ⟨1, Or.inr rfl, rfl, rfl⟩ | decide +kernel)

theorem noCircularExplanation (e : Explanation Entity Quality Feature)
    (h : AsymmetricGround e) (x f : Entity) (q : Quality) :
    NoCircularExplanation e x f q := by
  intro circle
  obtain ⟨forward, backward⟩ := circle
  have excludes := h (.exemplification x q) (.participation x f) forward
  exact excludes backward

theorem selectorAgreement (s t : Vocabulary Entity Quality)
    (e d : Explanation Entity Quality Feature) (feature : Feature)
    (h : SharedSelector s t e d feature) : ClassificationAgreement s t := by
  obtain ⟨hs, ht, baseAgreement, laws⟩ := h
  intro q f x hsq htq hsf htf hsx htx
  obtain ⟨slaw, tlaw⟩ := laws q f hsq htq hsf htf
  have left := hs q f x hsq hsf hsx
  have right := ht q f x htq htf htx
  exact left.trans ((slaw x hsx).trans ((baseAgreement x).trans
    ((tlaw x htx).symm.trans right.symm)))
end TruthCore.Results.Greek.Plato.ParticipationGrounding
