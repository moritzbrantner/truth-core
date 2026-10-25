import TruthCore.Modern.Hume.Induction
namespace TruthCore.Results.Modern.Hume.Induction
open TruthCore.Modern.Hume.Induction

private theorem finiteRecord : FiniteUnderdetermination := by
  intro n
  refine ⟨fun _ => true, delayedFailure n, ?_, ?_, rfl, ?_⟩
  · intro _ _; rfl
  · intro i hi
    exact ite_eq_left hi
  · exact ite_eq_right (Nat.lt_irrefl n)

private theorem interventions : InterventionUnderdetermination := by
  intro n
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro _ _; rfl
  · intro i hi
    exact ite_eq_left hi
  · exact ite_eq_right (Nat.lt_irrefl n)

private theorem conflicts : BridgeConflicts := by
  refine ⟨?_, ?_, ?_⟩
  · intro a hs hc
    have : Verdict.withheld = Verdict.entitled := (hs .habit).symm.trans hc
    cases this
  · intro a hs hb ⟨q, hq⟩
    have : Verdict.withheld = Verdict.entitled := (hs q).symm.trans (hb q hq)
    cases this
  · intro a basis standard x y same hs ht
    have h := standard x y same
    have : Verdict.entitled = Verdict.withheld := hs.symm.trans (h.trans ht)
    cases this

private theorem coverage : AnswerCoverage := by
  intro custom practice entitlement
  refine ⟨Or.inl rfl, Or.inr rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases h with h | h <;> cases h
  · intro h
    rcases h with h | h <;> cases h
  · intro h
    rcases h with h | h <;> cases h
  · intro h
    have ha := h.1.mpr (show (entitlementDemand entitlement).answers
      .nonCircularEntitlement from rfl)
    rcases ha with h | h <;> cases h

/-- Consequences, countermodels and coverage; no historical premise is proved. -/
theorem checks : Checks := by
  refine ⟨finiteRecord, interventions, conflicts, ?_, ?_, ?_, ?_, ?_, coverage⟩
  · intro _; exact ⟨rfl, rfl, rfl⟩
  · refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
    intro h
    have he := h .prediction rfl
    cases he
  · refine ⟨?_, ?_, ?_⟩
    · intro x y h; cases h; rfl
    · rfl
    · rfl
  · refine ⟨fun _ h => h, ?_⟩
    intro h
    cases h
  · refine ⟨fun h => h, ?_⟩
    intro h
    obtain ⟨f, hf, hfalse⟩ := h false
    have : (true : Bool) = false := (hf 0).symm.trans hfalse
    cases this

/-- Rejects an entitlement-denying reconstruction only if it certifies habit. -/
theorem selfApplication (a : Assessment) (hc : CertifiesHabit a) : RejectStrong a := by
  intro hs
  exact conflicts.1 a hs hc

/-- The normative bridge and practical reliance exclude blanket withholding. -/
theorem practice (a : Assessment) (hb : RelianceRequiresEntitlement a)
    (hr : SomeReliance a) : RejectStrong a := by
  intro hs
  exact conflicts.2.1 a hs hb hr

/-- Equal evidence and an invariant standard forbid selective withholding. -/
theorem selective (a : Assessment) (basis : Topic → Topic → Prop)
    (hu : UniformStandard a basis) (hs : SameScienceTheology basis)
    (he : ScienceEntitled a) : RejectTheologyWithheld a := by
  intro hw
  exact conflicts.2.2 a basis hu .science .theology hs he hw

end TruthCore.Results.Modern.Hume.Induction
