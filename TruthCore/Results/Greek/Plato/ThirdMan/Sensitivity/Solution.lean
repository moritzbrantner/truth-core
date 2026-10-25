import TruthCore.Greek.Plato.ThirdMan.Sensitivity
namespace TruthCore.Results.Greek.Plato.ThirdMan.Sensitivity
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ThirdMan

private theorem bounded (s : Vocabulary Small Unit)
    (h : ∀ f q, s.FormOf f q → f = .form) : ¬ UnboundedForms s := by
  rintro ⟨q,_,hunbounded⟩
  obtain ⟨fs,hlen,hpair,hforms⟩ := hunbounded 2
  cases fs with
  | nil => exact Nat.noConfusion hlen
  | cons f fs =>
    cases fs with
    | nil => exact Nat.noConfusion (Nat.succ.inj hlen)
    | cons g gs =>
      have hfg := (List.pairwise_cons.mp hpair).1 g (List.Mem.head _)
      exact hfg ((h f q (hforms f (List.Mem.head _))).trans (h g q (hforms g (List.Mem.tail f (List.Mem.head _)))).symm)

private theorem instances (s : Vocabulary Small Unit)
    (hPart : ∀ x, s.Particular x ↔ x ≠ .form)
    (hF : s.Exemplifies .a () ∧ s.Exemplifies .b ())
    (hAdmit : s.Admitted ()) : PropertyInstances s := by
  exact ⟨.a,.b,(),by decide,(hPart _).mpr (by decide),
    (hPart _).mpr (by decide),hAdmit,hF⟩

private theorem ni (s : Vocabulary Small Unit)
    (hForm : ∀ f q, s.FormOf f q → f = .form)
    (hPart : ∀ x f, s.Participates x f → x ≠ .form) : ParticipantNonidentity s := by
  intro q _ f x hf hx heq
  exact hPart x f hx (heq.symm.trans (hForm f q hf))

private theorem common (s : Vocabulary Small Unit)
    (hLike : ∀ y, ¬ s.Like .form y)
    (hForm : s.FormOf .form ())
    (hPart : ∀ x, x ≠ Small.form → s.Participates x .form) :
    LikenessFormation s (fun _ => True) () := by
  intro xs _ hplural hmutual
  refine ⟨.form,hForm,?_⟩
  intro x hx
  apply hPart x
  intro heq
  obtain ⟨first,ha,second,hb,hab⟩ := hplural
  by_cases hxa : x = first
  · have hh := hmutual x hx second hb (fun hxb => hab (hxa.symm.trans hxb))
    exact hLike second (heq ▸ hh)
  · exact hLike first (heq ▸ hmutual x hx first ha hxa)

/-- Each omitted principle has a concrete three-entity countermodel. -/
theorem sensitivityModels : SensitivityModels := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · refine ⟨small,?_,?_,?_,?_,?_,?_,bounded small (by intros; assumption)⟩
    · exact instances small (by intro; rfl) ⟨True.intro,True.intro⟩ True.intro
    · intro first second _ _; trivial
    · intro q _ f _; trivial
    · exact ni small (by intros; assumption) (by intro x f h; exact h.1)
    · intro q _ xs f _ _; trivial
    · intro hf
      obtain ⟨f,hform,hparts⟩ := hf () True.intro [.form,.a] True.intro
        ⟨.form,List.Mem.head _,.a,List.Mem.tail _ (List.Mem.head _),by decide⟩ (by intros; trivial)
      exact (hparts .form (List.Mem.head _)).1 rfl
  · refine ⟨nonSelf,?_,?_,?_,?_,?_,?_,?_,bounded nonSelf (by intros; assumption)⟩
    · exact instances nonSelf (by intro; rfl) ⟨by change Small.a ≠ Small.form; decide,by change Small.b ≠ Small.form; decide⟩ True.intro
    · intro first second _ _; trivial
    · intro q _ xs _ _ hF
      exact ⟨.form,rfl,fun x hx => ⟨hF x hx,rfl⟩⟩
    · exact ni nonSelf (by intros; assumption) (by intro x f h; exact h.1)
    · intro q _ xs f _ _; trivial
    · intro q _ f hf; exact hf
    · intro h; exact h () True.intro .form rfl rfl
  · refine ⟨selfParticipating,?_,?_,?_,?_,?_,?_,bounded selfParticipating (by intros; assumption)⟩
    · exact instances selfParticipating (by intro; rfl) ⟨True.intro,True.intro⟩ True.intro
    · intro first second _ _; trivial
    · intro q _ xs _ _ _; exact ⟨.form,rfl,by intros; rfl⟩
    · intro q _ f _; trivial
    · intro q _ xs f _ _; trivial
    · intro h; exact h () True.intro .form .form rfl rfl rfl
  · refine ⟨small,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,bounded small (by intros; assumption)⟩
    · exact instances small (by intro; rfl) ⟨True.intro,True.intro⟩ True.intro
    · intro first second ha hb x hx
      rcases pairCases hx with rfl | rfl
      · exact ha
      · exact hb
    · intro q _ xs helig _ _; exact ⟨.form,rfl,fun x hx => ⟨helig x hx,rfl⟩⟩
    · intro q _ f _; trivial
    · exact ni small (by intros; assumption) (by intro x f h; exact h.1)
    · intro q _; exact ⟨.form,rfl,fun x hx _ => ⟨hx,rfl⟩⟩
    · intro q _ f g hf hg; exact hf.trans hg.symm
    · intro q _ x hx _; exact ⟨.form,rfl,⟨hx,rfl⟩,rfl,hx⟩
    · intro q _ x hx _; exact ⟨.form,rfl,⟨rfl,hx⟩,hx,rfl⟩
    · intro q _ f hf; exact hf
    · intro h
      have he := h () True.intro [.a,.b] .form (by
        intro x hx; rcases pairCases hx with rfl | rfl <;> decide) rfl
      exact he .form (List.Mem.head _) rfl
  · refine ⟨directed,?_,?_,?_,?_,?_,?_,bounded directed (by intros; assumption)⟩
    · exact ⟨True.intro,.a,.b,by decide,True.intro,⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩
    · exact common directed (by intro y h; exact h.1 rfl) rfl (fun x hx => ⟨hx,rfl⟩)
    · intro x f hp
      exact ⟨hp.1,fun hxf => hp.1 (hxf.trans hp.2)⟩
    · exact ni directed (by intros; assumption) (by intro x f h; exact h.1)
    · intro q _ xs f _ _; trivial
    · intro h; exact (h .a .form (⟨by decide,by decide⟩)).1 rfl
  · refine ⟨nonResemblance,?_,?_,?_,?_,?_,?_,bounded nonResemblance (by intros; assumption)⟩
    · exact ⟨True.intro,.a,.b,by decide,True.intro,⟨by decide,by decide,by decide⟩,⟨by decide,by decide,by decide⟩⟩
    · exact common nonResemblance (by intro y h; exact h.1 rfl) rfl (fun x hx => ⟨hx,rfl⟩)
    · intro x y h; exact ⟨h.2.1,h.1,Ne.symm h.2.2⟩
    · exact ni nonResemblance (by intros; assumption) (by intro x f h; exact h.1)
    · intro q _ xs f _ _; trivial
    · intro h; exact (h .a .form ⟨by decide,rfl⟩).2.1 rfl
end TruthCore.Results.Greek.Plato.ThirdMan.Sensitivity
