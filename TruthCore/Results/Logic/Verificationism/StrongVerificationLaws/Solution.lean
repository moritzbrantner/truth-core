module

public import TruthCore.Logic.Verificationism
public import TruthCore.Logic.Verificationism.Model

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.StrongVerificationLaws
open TruthCore.Logic.Verificationism
/-- Strong verification excludes universal laws: in every law setting the law is not conclusively verifiable, while its negation is whenever an observed counterinstance is possible. -/
theorem strongVerificationExcludesLaws : StrongVerificationExcludesLaws := by
  intro L F U S
  constructor
  · intro ⟨os, hobs, ⟨w0, hw0⟩, hent⟩
    -- the finitely many individuals the verifying observations are about
    have hcover : ∃ l : List U.Individual, ∀ o, o ∈ os → ∀ a, S.mentions o a → a ∈ l := by
      clear hw0 hent
      induction os with
      | nil => exact ⟨[], fun o ho => nomatch ho⟩
      | cons o rest ih =>
        obtain ⟨l1, hl1⟩ := S.finite_mentions o (hobs o (List.Mem.head _))
        obtain ⟨l2, hl2⟩ := ih (fun g hg => hobs g (List.Mem.tail _ hg))
        refine ⟨l1 ++ l2, ?_⟩
        intro g hg a hm
        cases hg with
        | head => exact List.mem_append_left _ (hl1 a hm)
        | tail _ hg' => exact List.mem_append_right _ (hl2 g hg' a hm)
    obtain ⟨l, hl⟩ := hcover
    -- an individual none of them is about, made a non-black raven
    obtain ⟨a, ha⟩ := S.infinite l
    obtain ⟨w', hR, hB, hsame⟩ := S.vary w0 a
    have hall : ∀ g, g ∈ os → L.holds w' g := fun g hg =>
      (hsame g (hobs g hg) (fun hm => ha (hl g hg a hm))).mpr (hw0 g hg)
    exact hB (((U.holds_law w').mp (hent w' hall)) a hR)
  · intro a notB hRo hNo hiff hsat
    refine ⟨[U.R a, notB], ?_, hsat, ?_⟩
    · intro g hg
      cases hg with
      | head => exact hRo
      | tail _ h =>
        cases h with
        | head => exact hNo
        | tail _ h => cases h
    · intro v hv
      apply (L.holds_neg v _).mpr
      intro hlaw
      have hRa := hv _ (List.Mem.head _)
      have hnb := hv _ (List.Mem.tail _ (List.Mem.head _))
      exact (hiff v).mp hnb ((U.holds_law v).mp hlaw a hRa)
/-- The hypotheses are satisfiable: the raven language is a law setting. -/
theorem lawSettingInhabited :
    ∃ (L : Language) (F : Frame L) (U : UniversalLaw L), Nonempty (LawSetting F U) :=
  ⟨Model.lawLanguage, Model.lawFrame, Model.ravens, ⟨Model.ravensSetting⟩⟩
end TruthCore.Results.Logic.Verificationism.StrongVerificationLaws
