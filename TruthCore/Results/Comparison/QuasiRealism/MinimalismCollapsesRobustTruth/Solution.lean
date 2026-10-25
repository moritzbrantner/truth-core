import TruthCore.Refutations.QuasiRealism
namespace TruthCore.Results.Comparison.QuasiRealism.MinimalismCollapsesRobustTruth
open TruthCore.English.VanRoojen

/-- The collapse argument on the robust-truth deviation (#190). Every moral
sentence has the surface of an assertion and a disciplined use (Divers and
Miller), so by the minimalist sufficiency conditions it is minimally
truth-apt; if there is no truth-aptness more robust than the minimal, it is
robustly truth-apt. That is realism's answer to `Q-ROBUST-TRUTH`. -/
theorem minimalismCollapsesRobustTruth {Sentence : Type}
    (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt : Sentence → Prop)
    (hSufficiency :
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt)
    (hMoralMeets :
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse)
    (hNoRobustBeyond : NoRobustTruthAptnessBeyondMinimalReading TruthApt RobustlyTruthApt) :
    RealistRobustTruthAptReading Moral RobustlyTruthApt := by
  intro φ hMoral
  -- INF-MORAL-SENTENCES-MINIMALLY-TRUTH-APT: φ meets both constraints, so it is minimally truth-apt
  have hConstraints := hMoralMeets φ hMoral
  have hTruthApt : TruthApt φ := hSufficiency φ hConstraints.1 hConstraints.2
  -- INF-COLLAPSE-GIVES-ROBUST-TRUTH: no truth-aptness is more robust than the minimal
  exact hNoRobustBeyond φ hTruthApt

/-! ## The deviation cannot be sustained under the collapse premise -/

/-- With a moral sentence, the same premises are inconsistent with
quasi-realism's answer (minimally, not robustly, truth-apt): the minimal/robust
contrast cannot be drawn for moral sentences if the collapse premise holds. -/
theorem collapseExcludesQuasiRealistMinimalTruth {Sentence : Type}
    (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt : Sentence → Prop)
    (p : Sentence)
    (hSufficiency :
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt)
    (hMoralMeets :
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse)
    (hNoRobustBeyond : NoRobustTruthAptnessBeyondMinimalReading TruthApt RobustlyTruthApt)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    ¬ QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt := fun hQuasiRealism =>
  (hQuasiRealism p hMoral).2
    (minimalismCollapsesRobustTruth Moral SurfaceAssertoric DisciplinedUse TruthApt
      RobustlyTruthApt hSufficiency hMoralMeets hNoRobustBeyond p hMoral)

/-! ## Countermodels: each premise is needed

Each model has one moral sentence (`Unit`) that is not robustly truth-apt, so
realism's answer fails, while the two other premises hold. -/

/-- Without the sufficiency conditions: the sentence meets both constraints but
is not truth-apt, so the collapse premise holds vacuously. -/
theorem withoutSufficiencyNoCollapse :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt : Unit → Prop),
      ¬ MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      NoRobustTruthAptnessBeyondMinimalReading TruthApt RobustlyTruthApt ∧
      ¬ RealistRobustTruthAptReading Moral RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => False, fun _ => False,
    fun h => h () trivial trivial, fun _ _ => ⟨trivial, trivial⟩, fun _ h => h,
    fun h => h () trivial⟩

/-- Without Divers and Miller's finding: the moral sentence lacks the surface of
an assertion, so nothing makes it truth-apt. -/
theorem withoutMoralSentencesMeetingConstraintsNoCollapse :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt : Unit → Prop),
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      ¬ MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      NoRobustTruthAptnessBeyondMinimalReading TruthApt RobustlyTruthApt ∧
      ¬ RealistRobustTruthAptReading Moral RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => False, fun _ => True, fun _ => False, fun _ => False,
    fun _ h _ => h, fun h => (h () trivial).1, fun _ h => h,
    fun h => h () trivial⟩

/-- Without the collapse premise: the moral sentence is minimally but not
robustly truth-apt. This is the quasi-realist's own model, and quasi-realism's
answer holds in it. -/
theorem withoutCollapsePremiseNoCollapse :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt : Unit → Prop),
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      ¬ NoRobustTruthAptnessBeyondMinimalReading TruthApt RobustlyTruthApt ∧
      ¬ RealistRobustTruthAptReading Moral RobustlyTruthApt ∧
      QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => True, fun _ => False,
    fun _ _ _ => trivial, fun _ _ => ⟨trivial, trivial⟩, fun h => h () trivial,
    fun h => h () trivial, fun _ _ => ⟨trivial, id⟩⟩

end TruthCore.Results.Comparison.QuasiRealism.MinimalismCollapsesRobustTruth
