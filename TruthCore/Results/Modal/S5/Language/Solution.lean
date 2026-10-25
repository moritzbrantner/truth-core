import TruthCore.Modal.S5Research
namespace TruthCore.Results.Modal.S5.Language
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.S5Research
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

/-- A sharper proof obligation than global excluded middle: only admissible
truths at the collapsed witness need a decision. The bundled contract supplies
this from explicit excluded middle; it does not hide classical reasoning. -/
theorem local_agreement {W : Type} (F : Frame W) (D : Domain W) (v : W)
    (hDecision : ∀ P, D P → P v ∨ ¬ P v)
    (hNeg : ∀ P, D P → D (fun x => ¬ P x)) (hMC : MC F D v) :
    ∀ x, F.access v x → Agree D v x := by
  intro x hx P hp
  constructor
  · intro hpv; exact hMC P hp hpv x hx
  · intro hpx
    cases hDecision P hp with
    | inl hpv => exact hpv
    | inr hnpv => exact (hMC (fun y => ¬ P y) (hNeg P hp) hnpv x hx hpx).elim

theorem uniform {W : Type} (F : Frame W) (D : Domain W) (w : W)
    (hS5 : S5Frame F) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hNeg : ∀ P, D P → D (fun v => ¬ P v))
    (hPossible : Dia F (MC F D) w) : ComponentUniform F D w := by
  obtain ⟨v, hwv, hMC⟩ := hPossible
  have hs := (s5_implies_ktb F hS5).2
  have ht := (s5_implies_s4 F hS5).2
  intro a b hwa hwb P hp
  have hvw := hs w v hwv
  have ha := local_agreement F D v (fun P _ => hEM (P v)) hNeg hMC a (ht v w a hvw hwa) P hp
  have hb := local_agreement F D v (fun P _ => hEM (P v)) hNeg hMC b (ht v w b hvw hwb) P hp
  exact ha.symm.trans hb

theorem properties {W : Type} (F : Frame W) (D : Domain W) (w : W)
    (hS5 : S5Frame F) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hNeg : ∀ P, D P → D (fun v => ¬ P v))
    (hPossible : Dia F (MC F D) w) :
    ComponentUniform F D w ∧ MC F D w ∧ Box F (MC F D) w ∧
    (∀ P, D P → (Dia F P w ↔ P w)) ∧
    (∀ P, D P → ¬ Contingent F P w) := by
  have hu := uniform F D w hS5 hEM hNeg hPossible
  have hr := (s5_implies_ktb F hS5).1
  have ht := (s5_implies_s4 F hS5).2
  have ha : ∀ P, D P → (Dia F P w ↔ P w) := by
    intro P hp
    constructor
    · rintro ⟨v, hv, hpv⟩
      exact (hu w v (hr w) hv P hp).mpr hpv
    · intro hpw
      exact ⟨w, hr w, hpw⟩
  refine ⟨hu, ?_, ?_, ha, ?_⟩
  · intro P hp hpw v hv
    exact (hu w v (hr w) hv P hp).mp hpw
  · intro v hv P hp hpv z hvz
    exact (hu v z hv (ht w v z hv hvz) P hp).mp hpv
  · intro P hp hc
    exact ((ha (fun v => ¬ P v) (hNeg P hp)).mp hc.2) ((ha P hp).mp hc.1)

theorem identity {W : Type} (F : Frame W) (D : Domain W) (w : W)
    (hS5 : S5Frame F) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hNeg : ∀ P, D P → D (fun v => ¬ P v))
    (hExt : PropositionalExtensionality D) (hPossible : Dia F (MC F D) w) :
    ∀ v, F.access w v → v = w := by
  intro v hv
  have hu := uniform F D w hS5 hEM hNeg hPossible
  exact (hExt w v (hu w v ((s5_implies_ktb F hS5).1 w) hv)).symm

/-- Unlike a corpus inventory, the full formula language contains negations. -/
theorem expressible_negation_closed {W A : Type} (F : Frame W) (V : Valuation W A) :
    ∀ P, expressible F V P → expressible F V (fun v => ¬ P v) := by
  rintro P ⟨p, rfl⟩
  exact ⟨Formula.neg p, rfl⟩

theorem checks : LanguageLaws := by
  refine ⟨fun _ F D w hs he hn hp => properties F D w hs he hn hp,
    fun _ F D w hs he hn hx hp => identity F D w hs he hn hx hp, ?_⟩
  intro W F D w hs hu he hn hx hp v
  exact identity F D w hs he hn hx hp v (hu w v)
end TruthCore.Results.Modal.S5.Language
