import TruthCore.Modal.Convergence

namespace TruthCore.Results.Modal.Convergence
open TruthCore.Modal
universe u v

theorem exactPath_zero {World : Type u} (F : Frame World) (a b : World) :
    ExactPath F 0 a b ↔ a = b := by
  let := F.toQuiver
  constructor
  · rintro ⟨p, hp⟩
    exact p.eq_of_length_zero hp
  · rintro rfl
    exact ⟨Quiver.Path.nil, rfl⟩

theorem exactPath_succ {World : Type u} (F : Frame World) (n : Nat) (a b : World) :
    ExactPath F (n + 1) a b ↔ ∃ c, F.access a c ∧ ExactPath F n c b := by
  let := F.toQuiver
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨c, e, q, hq, _⟩ := p.eq_toPath_comp_of_length_eq_succ hp
    exact ⟨c, e.down, q, hq⟩
  · rintro ⟨c, e, q, hq⟩
    refine ⟨(@Quiver.Hom.toPath World F.toQuiver a c ⟨e⟩).comp q, ?_⟩
    rw [Quiver.Path.length_comp, Quiver.Path.length_toPath, hq, Nat.add_comm]

theorem iterBox_semantics {World : Type u} {Atom : Type v} (F : Frame World)
    (V : Valuation World Atom) (φ : Formula Atom) (n : Nat) (a : World) :
    Holds F V a (.iterBox n φ) ↔ ∀ b, ExactPath F n a b → Holds F V b φ := by
  induction n generalizing a with
  | zero =>
      simp only [Formula.iterBox, exactPath_zero]
      exact ⟨fun h b hab => hab ▸ h, fun h => h a rfl⟩
  | succ n ih =>
      change (∀ c, F.access a c → Holds F V c (.iterBox n φ)) ↔ _
      simp only [ih, exactPath_succ]
      constructor
      · intro h b ⟨c, hac, hcb⟩
        exact h c hac b hcb
      · intro h c hac b hcb
        exact h b ⟨c, hac, hcb⟩

theorem iterDiamond_semantics {World : Type u} {Atom : Type v} (F : Frame World)
    (V : Valuation World Atom) (φ : Formula Atom) (n : Nat) (a : World) :
    Holds F V a (.iterDiamond n φ) ↔ ∃ b, ExactPath F n a b ∧ Holds F V b φ := by
  induction n generalizing a with
  | zero =>
      simp only [Formula.iterDiamond, exactPath_zero]
      exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨b, hab, hb⟩ => hab.symm ▸ hb⟩
  | succ n ih =>
      change (∃ c, F.access a c ∧ Holds F V c (.iterDiamond n φ)) ↔ _
      simp only [ih, exactPath_succ]
      constructor
      · rintro ⟨c, hac, b, hcb, hb⟩
        exact ⟨b, ⟨c, hac, hcb⟩, hb⟩
      · rintro ⟨b, ⟨c, hac, hcb⟩, hb⟩
        exact ⟨c, hac, b, hcb, hb⟩

/-- Soundness covers arbitrary formulas, not only the one-atom test. -/
theorem convergence_sound {World : Type u} {Atom : Type v} (F : Frame World)
    (h i j k : Nat) (hc : Convergent F h i j k) (φ : Formula Atom) :
    Valid F (.imp (.iterDiamond h (.iterBox i φ)) (.iterBox j (.iterDiamond k φ))) := by
  intro V w hAnte
  obtain ⟨a, hwa, ha⟩ := (iterDiamond_semantics F V (.iterBox i φ) h w).mp hAnte
  apply (iterBox_semantics F V (.iterDiamond k φ) j w).mpr
  intro b hwb
  obtain ⟨c, hac, hbc⟩ := hc w a b hwa hwb
  apply (iterDiamond_semantics F V φ k b).mpr
  exact ⟨c, hbc, (iterBox_semantics F V φ i a).mp ha c hac⟩

/-- Characteristic valuations give correspondence, without a completeness claim. -/
theorem convergence_iff_valid {World : Type u} (F : Frame World) (h i j k : Nat) :
    Convergent F h i j k ↔ Valid F (convergenceFormula h i j k) := by
  constructor
  · intro hc
    exact convergence_sound F h i j k hc (.atom ())
  · intro hv w a b hwa hwb
    let V : Valuation World Unit := fun z _ => ExactPath F i a z
    have ha : Holds F V a (.iterBox i (.atom ())) :=
      (iterBox_semantics F V (.atom ()) i a).mpr (fun c hc => hc)
    have hw := (iterDiamond_semantics F V (.iterBox i (.atom ())) h w).mpr ⟨a, hwa, ha⟩
    have hb := (iterBox_semantics F V (.iterDiamond k (.atom ())) j w).mp (hv V w hw) b hwb
    obtain ⟨c, hbc, hac⟩ := (iterDiamond_semantics F V (.atom ()) k b).mp hb
    exact ⟨c, hac, hbc⟩

private theorem exactPath_one {World : Type u} (F : Frame World) (a b : World) :
    ExactPath F 1 a b ↔ F.access a b := by
  rw [exactPath_succ]
  simp only [exactPath_zero]
  exact ⟨fun ⟨c, hac, hcb⟩ => hcb ▸ hac, fun h => ⟨b, h, rfl⟩⟩

theorem axiom4_correspondence {World : Type u} (F : Frame World) :
    Transitive F ↔ Valid F (convergenceFormula 0 1 2 0) := by
  constructor
  · intro ht
    simpa only [convergenceFormula, Formula.iterDiamond, Formula.iterBox] using
      axiom4_valid F ht (.atom ())
  · intro hv w a b hwa hab
    have hc := (convergence_iff_valid F 0 1 2 0).mpr hv
    have hw : ExactPath F 0 w w := (exactPath_zero F w w).mpr rfl
    have hb : ExactPath F 2 w b := (exactPath_succ F 1 w b).mpr
      ⟨a, hwa, (exactPath_one F a b).mpr hab⟩
    obtain ⟨c, hwc, hbc⟩ := hc w w b hw hb
    have heq := (exactPath_zero F b c).mp hbc
    exact heq.symm ▸ (exactPath_one F w c).mp hwc

theorem axiomB_correspondence {World : Type u} (F : Frame World) :
    Symmetric F ↔ Valid F (convergenceFormula 0 0 1 1) := by
  constructor
  · intro hs
    simpa only [convergenceFormula, Formula.iterDiamond, Formula.iterBox] using
      axiomB_valid F hs (.atom ())
  · intro hv w a hwa
    have hc := (convergence_iff_valid F 0 0 1 1).mpr hv
    obtain ⟨c, hwc, hac⟩ := hc w w a ((exactPath_zero F w w).mpr rfl)
      ((exactPath_one F w a).mpr hwa)
    have heq := (exactPath_zero F w c).mp hwc
    exact heq.symm ▸ (exactPath_one F a c).mp hac

theorem axiom5_correspondence {World : Type u} (F : Frame World) :
    Euclidean F ↔ Valid F (convergenceFormula 1 0 1 1) := by
  constructor
  · intro he
    simpa only [convergenceFormula, Formula.iterDiamond, Formula.iterBox] using
      axiom5_valid F he (.atom ())
  · intro hv w a b hwa hwb
    have hc := (convergence_iff_valid F 1 0 1 1).mpr hv
    obtain ⟨c, hbc, hac⟩ := hc w b a ((exactPath_one F w b).mpr hwb)
      ((exactPath_one F w a).mpr hwa)
    have heq := (exactPath_zero F b c).mp hbc
    exact heq.symm ▸ (exactPath_one F a c).mp hac
end TruthCore.Results.Modal.Convergence
