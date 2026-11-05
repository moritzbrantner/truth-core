module

public import TruthCore.Logic.Verificationism.NegationClosure
public import TruthCore.Results.Logic.Verificationism.StrongVerificationLaws.Solution

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.StrongVerificationClosure
open TruthCore.Logic.Verificationism

/-- In a law setting, no sentence that implies the law's double negation at
every world is conclusively verifiable. The same argument as for the law
itself (`strongVerificationExcludesLaws`), with the double negation in its
place. -/
theorem not_conclusive_of_implies_not_not_law {L : Language} {F : Frame L} {U : UniversalLaw L}
    (S : LawSetting F U) (t : L.Sentence)
    (ht : ∀ w, L.holds w t → ¬ ¬ L.holds w U.law) : ¬ ConclusivelyVerifiable F t := by
  intro ⟨os, hobs, ⟨w0, hw0⟩, hent⟩
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
  obtain ⟨a, ha⟩ := S.infinite l
  obtain ⟨w', hR, hB, hsame⟩ := S.vary w0 a
  have hall : ∀ g, g ∈ os → L.holds w' g := fun g hg =>
    (hsame g (hobs g hg) (fun hm => ha (hl g hg a hm))).mpr (hw0 g hg)
  exact ht w' (hent w' hall) (fun hlaw => hB (((U.holds_law w').mp hlaw) a hR))

/-- Defeat 2 counted: with meaningfulness closed under negation for negated
sentences (the weak version), the V1 package fails. The negation of a testable law is conclusively verifiable, hence
meaningful; so its double negation is meaningful; but the double negation is
neither analytic (it fails where the counterinstance holds) nor conclusively
verifiable. -/
theorem strongVerificationismWithLawsFails {L : Language} (F : Frame L)
    (meaningful : L.Sentence → Prop) (hClosed : MeaningClosedUnderNegationOfNegations L meaningful) :
    StrongVerificationismWithLawsFails F meaningful := by
  intro ⟨hValid, hCrit, U, ⟨S⟩, a, notB, hRo, hNo, hiff, hsat⟩
  have hNegCV := (StrongVerificationLaws.strongVerificationExcludesLaws L F U S).2
    a notB hRo hNo hiff hsat
  have hNegMeaningful : meaningful (L.neg U.law) := (hCrit _).mpr (Or.inr hNegCV)
  have hDouble : meaningful (L.neg (L.neg U.law)) := hClosed _ hNegMeaningful
  -- the double negation fails where the counterinstance holds
  obtain ⟨w, hw⟩ := hsat
  have hLawFails : ¬ L.holds w U.law := fun hlaw =>
    (hiff w).mp (hw notB (List.Mem.tail _ (List.Mem.head _)))
      ((U.holds_law w).mp hlaw a (hw _ (List.Mem.head _)))
  have hDN : ∀ v, L.holds v (L.neg (L.neg U.law)) → ¬ ¬ L.holds v U.law := fun v h =>
    (L.holds_neg v _).mp h ∘ (L.holds_neg v _).mpr
  rcases (hCrit _).mp hDouble with hAn | hCV
  · exact hDN w (hValid _ hAn w) hLawFails
  · exact not_conclusive_of_implies_not_not_law S _ hDN hCV

end TruthCore.Results.Logic.Verificationism.StrongVerificationClosure
