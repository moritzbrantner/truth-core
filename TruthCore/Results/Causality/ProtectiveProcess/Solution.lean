module
public import TruthCore.Causality.ProtectiveProcess
@[expose] public section
namespace TruthCore.Results.Causality.ProtectiveProcess
open TruthCore.Causality.ProtectiveProcess
open TruthCore.Causality.PreservationCandidates
open Stage

theorem safety : Safety := by
  intro B P S m blocked h bound b initial admiss covered complete n hn
  induction n with
  | zero => exact initial
  | succ n ih =>
    have lt : n < bound := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    rcases covered n lt (ih (Nat.le_of_lt lt)) with present | ⟨p, destroys⟩
    · exact present
    · exact False.elim (admiss n lt p (complete n lt p destroys) destroys.1)

/-- Pure projection of the declared realization bridge, not a new proof of
its applicability or a physical intervention mechanism. -/
theorem actionProjection : ActionProjection := by
  intro B P S m a h bound realized
  obtain ⟨t, role, target, ongoing, _⟩ := realized
  exact ⟨t, role, target, ongoing⟩

private theorem underTwo (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    cases n with
    | zero => exact Or.inr rfl
    | succ n =>
      exact False.elim (Nat.not_lt_of_ge
        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) h)

private instance (p : Bool) (s t : Stage) : Decidable (finite.occurs p s t) := by
  unfold finite
  infer_instance
private instance (p : Bool) (s t : Stage) (b : Bool) : Decidable (Destroys finite p s t b) := by
  unfold Destroys finite
  infer_instance
private instance (s : Stage) (b : Bool) : Decidable (finite.existsAt s b) := by
  unfold finite
  infer_instance

theorem controls : Controls := by
  have guardAd : Admissible finite blockFlame guarded 2 := by
    intro n hn p hp he
    change p = false at hp
    subst p
    have casesN : n = 0 ∨ n = 1 := underTwo n hn
    rcases casesN with rfl | rfl <;> revert he <;> decide
  have guardNo : NoBypass finite blockFlame guarded 2 true := by
    intro n hn p he
    have casesN : n = 0 ∨ n = 1 := underTwo n hn
    rcases casesN with rfl | rfl <;> cases he.2.1
  have guardAll : ∀ n, finite.existsAt (guarded n) true := by
    intro n
    cases n with
    | zero => exact Or.inr (by decide)
    | succ n => exact Or.inr (by rw [← Nat.succ_eq_add_one]; exact Stage.noConfusion)
  have guardCov : LossCovered finite guarded 2 true := by
    intro n hn he
    exact Or.inl (guardAll (n+1))
  have guardSafe : ProtectedInterval finite guarded 2 true := by
    intro n hn
    exact guardAll n
  have flameHit : Destroys finite false (flame 1) (flame 2) true := by decide
  have flameLost : ¬ ProtectedInterval finite flame 2 true := by
    intro hs
    exact (by decide : ¬ finite.existsAt (flame 2) true) (hs 2 (by decide))
  have bypassAd : Admissible finite blockFlame bypass 1 := by
    intro n hn p hp he
    change p = false at hp
    subst p
    have : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
    subst n
    revert he
    decide
  have replaceAd : Admissible finite blockFlame replacement 2 := by
    intro n hn p hp he
    change p = false at hp
    subst p
    have casesN : n = 0 ∨ n = 1 := underTwo n hn
    rcases casesN with rfl | rfl <;> revert he <;> decide
  refine ⟨⟨?_, guardAd, guardCov, guardNo, guardSafe⟩,
    ⟨removed_threat_absent _ _, flameHit, flameLost⟩,
    ⟨bypassAd, ?_, ?_, ?_⟩, ⟨replaceAd, ?_, ?_, ?_⟩,
    ⟨removed_threat_absent _ _, ?_, flameLost⟩, ⟨?_, ?_, ?_, flameLost⟩, ?_, ?_, ?_⟩
  · exact ⟨rfl, by decide, by decide⟩
  · intro n hn _
    have : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
    subst n
    exact Or.inr ⟨true, by decide⟩
  · intro hc
    have := hc 0 (by decide) true (by decide)
    cases this
  · intro hs
    exact (by decide : ¬ finite.existsAt (bypass 1) true) (hs 1 (by decide))
  · intro n hn _
    have casesN : n = 0 ∨ n = 1 := underTwo n hn
    rcases casesN with rfl | rfl
    · exact Or.inl (Or.inr (by decide))
    · exact Or.inr ⟨true, by decide⟩
  · intro hc
    have := hc 1 (by decide) true (by decide)
    cases this
  · intro hs
    exact (by decide : ¬ finite.existsAt (replacement 2) true) (hs 2 (by decide))
  · intro n hn p hp
    have ht := congrArg Threat.target hp
    cases ht
  · intro n hn _
    have casesN : n = 0 ∨ n = 1 := underTwo n hn
    rcases casesN with rfl | rfl
    · exact Or.inl (Or.inr (by decide))
    · exact Or.inr ⟨false, flameHit⟩
  · intro n hn p he
    have casesN : n = 0 ∨ n = 1 := underTwo n hn
    rcases casesN with rfl | rfl
    · cases he.2.1
    · cases p
      · rfl
      · have introImpossible : False := (by decide : ¬ Destroys finite true (flame 1) (flame 2) true) he
        exact introImpossible.elim
  · intro ha
    exact ha 0 (by decide) false rfl (by decide)
  · let m : Model Bool Bool Stage := { finite with existsAt := fun s _ => s = ready }
    refine ⟨m, rfl, guardAd, guardNo, rfl, ?_, ?_⟩
    · intro hc
      rcases hc 0 (by decide) rfl with h | ⟨p, h⟩
      · cases h
      · cases h.2.1
    · intro hs
      have := hs 1 (by decide)
      cases this
  · let m : Model Bool Bool Stage := { finite with existsAt := fun _ _ => False }
    refine ⟨m, id, guardAd, ?_, guardNo, ?_⟩
    · intro n hn he
      exact he.elim
    · intro hs
      exact hs 0 (by decide)
  · refine ⟨fun _ _ _ => False, ?_, guardSafe, fun _ _ _ h => h⟩
    refine ⟨⟨false, true⟩, rfl, rfl, trivial, ?_⟩
    intro n hn p hp
    apply guardAd n hn p
    exact congrArg Threat.source hp
end TruthCore.Results.Causality.ProtectiveProcess
