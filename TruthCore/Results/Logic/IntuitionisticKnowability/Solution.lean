module

public import TruthCore.Logic.IntuitionisticKnowability
public import TruthCore.Results.Logic.FitchKnowability.Solution
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

@[expose] public section

namespace TruthCore.Results.Logic.IntuitionisticKnowability
open OrderDual TruthCore.Logic.IntuitionisticKnowability

private theorem persistent (p : Content) {u v : World}
    (huv : u ≤ v) (hp : holds p u) : holds p v :=
  (ofDual p).upper huv hp

private theorem ext {p q : Content} (h : ∀ w, holds p w ↔ holds q w) : p = q :=
  UpperSet.ext (Set.ext h)

private theorem le_of_holds {p q : Content}
    (h : ∀ w, holds p w → holds q w) : p ≤ q := h

private theorem holds_of_le {p q : Content} (h : p ≤ q) {w : World}
    (hp : holds p w) : holds q w := h hp

private theorem hInf (p q : Content) (w : World) :
    holds (p ⊓ q) w ↔ holds p w ∧ holds q w := Iff.rfl

private theorem hSup (p q : Content) (w : World) :
    holds (p ⊔ q) w ↔ holds p w ∨ holds q w := Iff.rfl

private theorem hTop (w : World) : holds ⊤ w := True.intro

private theorem hBot (w : World) : ¬ holds ⊥ w := id

private theorem hImp (p q : Content) (w : World) :
    holds (p ⇨ q) w ↔ ∀ v, w ≤ v → holds p v → holds q v := by
  constructor
  · intro h v hwv hp
    have hv := persistent (p ⇨ q) hwv h
    exact holds_of_le (himp_inf_le : (p ⇨ q) ⊓ p ≤ q) ⟨hv, hp⟩
  · intro h
    let cone : Content := toDual (UpperSet.Ici w)
    have bound : cone ⊓ p ≤ q := by
      apply le_of_holds
      intro v hv
      exact h v hv.1 hv.2
    have lift : cone ≤ p ⇨ q := le_himp_iff.mpr bound
    exact holds_of_le lift (show holds cone w from by change w ≤ w; exact le_rfl)

private theorem hNeg (p : Content) (w : World) :
    holds pᶜ w ↔ ∀ v, w ≤ v → ¬ holds p v := by
  rw [← himp_bot]
  exact hImp p ⊥ w

/-- Future implication and negation are the actual Mathlib Heyting operations. -/
theorem forcingBridge : FutureForcing := ⟨hImp, hNeg⟩

private theorem eRefl : TruthCore.Modal.Reflexive epistemic := by
  intro w
  exact (TruthCore.Results.Logic.FitchKnowability.restrictedSurvivor).2.1 (includeWorld w)

private theorem rawShape (p : Content) (w : World) :
    relational.knows (holds p) w ↔
      if w.val < 2 then holds p 0 else holds p 2 := by
  change (∀ v, epistemic.access w v → holds p v) ↔ _
  fin_cases w
  · constructor
    · intro h
      exact h 0 (by simp [epistemic, includeWorld,
        TruthCore.Logic.FitchKnowability.survivorEpistemic])
    · intro h v hv
      change holds p 0 at h
      fin_cases v
      · exact h
      · exact persistent p (by decide : (0 : World) ≤ 1) h
      · simp [epistemic, includeWorld,
          TruthCore.Logic.FitchKnowability.survivorEpistemic] at hv
  · constructor
    · intro h
      exact h 0 (by simp [epistemic, includeWorld,
        TruthCore.Logic.FitchKnowability.survivorEpistemic])
    · intro h v hv
      change holds p 0 at h
      fin_cases v
      · exact h
      · exact persistent p (by decide : (0 : World) ≤ 1) h
      · simp [epistemic, includeWorld,
          TruthCore.Logic.FitchKnowability.survivorEpistemic] at hv
  · constructor
    · intro h
      exact h 2 (by simp [epistemic, includeWorld,
        TruthCore.Logic.FitchKnowability.survivorEpistemic])
    · intro h v hv
      change holds p 2 at h
      fin_cases v
      · simp [epistemic, includeWorld,
          TruthCore.Logic.FitchKnowability.survivorEpistemic] at hv
      · simp [epistemic, includeWorld,
          TruthCore.Logic.FitchKnowability.survivorEpistemic] at hv
      · exact h

private theorem rawPersistent (p : Content) :
    IsUpperSet {w | relational.knows (holds p) w} := by
  intro u v huv h
  change relational.knows (holds p) u at h
  change relational.knows (holds p) v
  rw [rawShape] at h ⊢
  fin_cases u <;> fin_cases v <;>
    simp_all only [Fin.reduceFinMk, Fin.reduceLE]
  all_goals exact persistent p (by decide) h

private theorem kExact (p : Content) (w : World) :
    holds (knows p) w ↔ relational.knows (holds p) w := by
  change (∃ u, relational.knows (holds p) u ∧ u ≤ w) ↔ _
  constructor
  · rintro ⟨u, hu, huw⟩
    exact rawPersistent p huw hu
  · intro h
    exact ⟨w, h, le_rfl⟩

private theorem dExact (p : Content) (w : World) :
    holds (possible p) w ↔ ∃ v, modal.access w v ∧ holds p v := by
  change (∃ u, (∃ v, modal.access u v ∧ holds p v) ∧ u ≤ w) ↔ _
  constructor
  · rintro ⟨_, ⟨v, _, hp⟩, _⟩
    exact ⟨v, True.intro, hp⟩
  · intro h
    exact ⟨w, h, le_rfl⟩

private theorem operators : OperatorsExact := by
  refine ⟨kExact, dExact, ?_⟩
  intro p w
  rw [dExact]
  constructor
  · rintro ⟨v, hwv, hp⟩
    exact ⟨v, hwv, (kExact p v).mp hp⟩
  · rintro ⟨v, hwv, hp⟩
    exact ⟨v, hwv, (kExact p v).mpr hp⟩

private theorem frames : FrameProfile := by
  have old := TruthCore.Results.Logic.FitchKnowability.restrictedSurvivor
  refine ⟨eRefl, ?_, ?_, (fun _ => True.intro), (fun _ _ _ => True.intro),
    (fun _ _ _ _ _ => True.intro), (fun _ _ _ => True.intro)⟩
  · intro u v h
    exact old.2.2.1 (includeWorld u) (includeWorld v) h
  · intro u v w h₁ h₂
    exact old.2.2.2.1 (includeWorld u) (includeWorld v) (includeWorld w) h₁ h₂

private theorem leFinal (w : World) : w ≤ 2 := by
  fin_cases w <;> decide

private theorem kFinal (p : Content) : holds (knows p) 2 ↔ holds p 2 :=
  (kExact p 2).trans (rawShape p 2)

private theorem negFinal (p : Content) (w : World) :
    holds pᶜ w ↔ ¬ holds p 2 := by
  rw [hNeg]
  constructor
  · intro h
    exact h 2 (leFinal w)
  · intro h v _ hp
    exact h (persistent p (leFinal v) hp)

private theorem kMono {p q : Content} (hpq : p ≤ q) : knows p ≤ knows q := by
  apply le_of_holds
  intro w h
  apply (kExact q w).mpr
  intro v hwv
  exact holds_of_le hpq ((kExact p w).mp h v hwv)

private theorem kTop : knows ⊤ = ⊤ := by
  apply ext
  intro w
  constructor
  · intro _
    exact hTop w
  · intro _
    apply (kExact ⊤ w).mpr
    intro v _
    exact hTop v

private theorem kInf (p q : Content) : knows (p ⊓ q) = knows p ⊓ knows q := by
  apply ext
  intro w
  rw [hInf, kExact, kExact, kExact]
  constructor
  · intro h
    exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩
  · rintro ⟨hp, hq⟩ v hv
    exact ⟨hp v hv, hq v hv⟩

private theorem kFactive (p : Content) : knows p ≤ p := by
  apply le_of_holds
  intro w h
  exact (kExact p w).mp h w (eRefl w)

private theorem kDistribution (p q : Content) : knows (p ⇨ q) ≤ knows p ⇨ knows q := by
  apply le_himp_iff.mpr
  rw [← kInf]
  exact kMono himp_inf_le

private theorem kFour (p : Content) : knows p ≤ knows (knows p) := by
  apply le_of_holds
  intro w h
  apply (kExact (knows p) w).mpr
  intro v hwv
  apply (kExact p v).mpr
  intro u hvu
  exact (kExact p w).mp h u (frames.2.2.1 w v u hwv hvu)

private theorem kNegativeFive (p : Content) : (knows p)ᶜ ≤ knows ((knows p)ᶜ) := by
  apply le_of_holds
  intro w h
  apply (kExact (knows p)ᶜ w).mpr
  intro v _
  exact (negFinal (knows p) v).mpr ((negFinal (knows p) w).mp h)

private theorem laws : EpistemicLaws :=
  ⟨kTop, kInf, kFactive, kDistribution, kFour, kNegativeFive⟩

private theorem fullForward : FullForward := by
  intro p
  apply le_of_holds
  intro w hp
  apply (dExact (knows p) w).mpr
  exact ⟨2, True.intro, (kFinal p).mpr (persistent p (leFinal w) hp)⟩

private theorem mooreBottom (p : Content) : moore p = ⊥ := by
  apply ext
  intro w
  constructor
  · intro h
    change holds p w ∧ holds (knows p)ᶜ w at h
    exact False.elim (((negFinal (knows p) w).mp h.2)
      ((kFinal p).mpr (persistent p (leFinal w) h.1)))
  · intro h
    exact False.elim (hBot w h)

private theorem kBottom : knows ⊥ = ⊥ := bot_unique (kFactive ⊥)

private theorem mooreUnknowable : MooreUnknowable := by
  refine ⟨mooreBottom, ?_⟩
  intro p
  rw [mooreBottom, kBottom]

private theorem doubleNegated : DoubleNegatedConsequence := by
  intro p
  apply le_of_holds
  intro w hp
  apply (negFinal (knows p)ᶜ w).mpr
  intro h
  exact ((negFinal (knows p) 2).mp h)
    ((kFinal p).mpr (persistent p (leFinal w) hp))

private theorem atomAtMiddle : holds atom actual := by
  change (1 : World) ≤ 1
  decide
private theorem atomAtFinal : holds atom 2 := by
  change (1 : World) ≤ 2
  decide
private theorem atomNotAtZero : ¬ holds atom 0 := by
  change ¬ (1 : World) ≤ 0
  decide

private theorem middleNotKnown : ¬ holds (knows atom) actual := by
  intro h
  exact atomNotAtZero ((rawShape atom actual).mp ((kExact atom actual).mp h))

private theorem middleNotNegatedKnowledge : ¬ holds (knows atom)ᶜ actual := by
  intro h
  exact ((negFinal (knows atom) actual).mp h) ((kFinal atom).mpr atomAtFinal)

private theorem middleDouble : holds (knows atom)ᶜᶜ actual :=
  holds_of_le (doubleNegated atom) atomAtMiddle

private theorem stabilityFails : ¬ holds ((knows atom)ᶜᶜ ⇨ knows atom) actual := by
  intro h
  exact middleNotKnown ((hImp _ _ actual).mp h actual le_rfl middleDouble)

private theorem excludedMiddleFails : ¬ holds (knows atom ⊔ (knows atom)ᶜ) actual := by
  intro h
  rcases (hSup _ _ actual).mp h with h | h
  · exact middleNotKnown h
  · exact middleNotNegatedKnowledge h

/-- The complete same-model certificate; no old pointwise-negation theorem is
silently instantiated as an intuitionistic forcing theorem. -/
theorem survivor : JointSurvivor := by
  exact ⟨forcingBridge, operators, frames, laws, fullForward, mooreUnknowable,
    doubleNegated, atomAtMiddle, middleNotKnown, middleNotNegatedKnowledge,
    middleDouble, stabilityFails, excludedMiddleFails⟩

end TruthCore.Results.Logic.IntuitionisticKnowability
