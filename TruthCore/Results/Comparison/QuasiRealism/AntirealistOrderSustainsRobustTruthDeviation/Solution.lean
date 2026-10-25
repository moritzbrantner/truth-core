import TruthCore.Results.Comparison.QuasiRealism.MinimalismCollapsesRobustTruth.Solution
namespace TruthCore.Results.Comparison.QuasiRealism.AntirealistOrderSustainsRobustTruthDeviation
open TruthCore.English.VanRoojen
open TruthCore.Refutations.QuasiRealism
open TruthCore.Results.Comparison.QuasiRealism.MinimalismCollapsesRobustTruth

/-- The quasi-realist regroup on the robust-truth deviation (#190), with
Dreier's criterion. Every moral sentence is minimally truth-apt (the same
minimalist premises as the collapse argument). It is not robustly truth-apt:
robust moral truth would explain our thought and talk with the sentence
(Dreier's criterion), but on the anti-realist order our thought and talk
explain its truth instead, and the two orders exclude each other. So
quasi-realism's answer to `Q-ROBUST-TRUTH` follows. -/
theorem antirealistOrderSustainsRobustTruthDeviation {Sentence : Type}
    (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt
      TalkExplainsTruth TruthExplainsTalk : Sentence → Prop)
    (hSufficiency :
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt)
    (hMoralMeets :
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse)
    (hRobustExplains :
      RobustMoralTruthIsExplanatoryReading Moral RobustlyTruthApt TruthExplainsTalk)
    (hAntirealistOrder : AntirealistOrderOfExplanationReading Moral TalkExplainsTruth)
    (hAsymmetric : ExplanatoryOrderAsymmetric Moral TalkExplainsTruth TruthExplainsTalk) :
    QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt := by
  intro φ hMoral
  -- INF-MORAL-SENTENCES-MINIMALLY-TRUTH-APT: φ meets both constraints, so it is minimally truth-apt
  have hConstraints := hMoralMeets φ hMoral
  have hTruthApt : TruthApt φ := hSufficiency φ hConstraints.1 hConstraints.2
  -- INF-ANTIREALIST-ORDER-EXCLUDES-ROBUST-TRUTH: robust truth would explain the talk,
  -- but the talk explains the truth, and the orders exclude each other
  have hNotExplanatory : ¬ TruthExplainsTalk φ :=
    hAsymmetric φ hMoral (hAntirealistOrder φ hMoral)
  have hNotRobust : ¬ RobustlyTruthApt φ := fun hRobust =>
    hNotExplanatory (hRobustExplains φ hMoral hRobust)
  exact ⟨hTruthApt, hNotRobust⟩

/-! ## The crux: the collapse premise against the order of explanation -/

/-- With a moral sentence, the same premises refute the collapse premise: by
`minimalismCollapsesRobustTruth` it would make the sentence robustly truth-apt,
which the anti-realist order excludes. -/
theorem antirealistOrderExcludesCollapse {Sentence : Type}
    (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt
      TalkExplainsTruth TruthExplainsTalk : Sentence → Prop)
    (p : Sentence)
    (hSufficiency :
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt)
    (hMoralMeets :
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse)
    (hRobustExplains :
      RobustMoralTruthIsExplanatoryReading Moral RobustlyTruthApt TruthExplainsTalk)
    (hAntirealistOrder : AntirealistOrderOfExplanationReading Moral TalkExplainsTruth)
    (hAsymmetric : ExplanatoryOrderAsymmetric Moral TalkExplainsTruth TruthExplainsTalk)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    ¬ NoRobustTruthAptnessBeyondMinimalReading TruthApt RobustlyTruthApt := fun hNoRobustBeyond =>
  collapseExcludesQuasiRealistMinimalTruth Moral SurfaceAssertoric DisciplinedUse TruthApt
    RobustlyTruthApt p hSufficiency hMoralMeets hNoRobustBeyond hMoral
    (antirealistOrderSustainsRobustTruthDeviation Moral SurfaceAssertoric DisciplinedUse TruthApt
      RobustlyTruthApt TalkExplainsTruth TruthExplainsTalk hSufficiency hMoralMeets
      hRobustExplains hAntirealistOrder hAsymmetric)

/-- The data the quasi-realist accepts do not require realism's robust answer:
the minimalist sufficiency conditions, Divers and Miller's finding and
quasi-realism's own answer all hold of a moral sentence that is not robustly
truth-apt. Realism's answer needs a further premise, such as the collapse
premise, that the quasi-realist rejects. -/
theorem quasiRealistDataDoNotRequireRobustTruth :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt : Unit → Prop),
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt ∧
      GeachMinorPremiseIsMoralReading Moral () ∧
      ¬ RealistRobustTruthAptReading Moral RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => True, fun _ => False,
    fun _ _ _ => trivial, fun _ _ => ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, id⟩, trivial,
    fun h => h () trivial⟩

/-! ## Countermodels: each premise is needed

Each model has one moral sentence (`Unit`) for which quasi-realism's answer
fails, while the other four premises hold. -/

/-- Without the sufficiency conditions: nothing is truth-apt. -/
theorem withoutSufficiencyNotSustained :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt
        TalkExplainsTruth TruthExplainsTalk : Unit → Prop),
      ¬ MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      RobustMoralTruthIsExplanatoryReading Moral RobustlyTruthApt TruthExplainsTalk ∧
      AntirealistOrderOfExplanationReading Moral TalkExplainsTruth ∧
      ExplanatoryOrderAsymmetric Moral TalkExplainsTruth TruthExplainsTalk ∧
      ¬ QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => False, fun _ => False,
    fun _ => True, fun _ => False,
    fun h => h () trivial trivial, fun _ _ => ⟨trivial, trivial⟩, fun _ _ h => h.elim,
    fun _ _ => trivial, fun _ _ _ h => h, fun h => (h () trivial).1⟩

/-- Without Divers and Miller's finding: the moral sentence lacks the surface of
an assertion and is not truth-apt. -/
theorem withoutMoralSentencesMeetingConstraintsNotSustained :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt
        TalkExplainsTruth TruthExplainsTalk : Unit → Prop),
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      ¬ MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      RobustMoralTruthIsExplanatoryReading Moral RobustlyTruthApt TruthExplainsTalk ∧
      AntirealistOrderOfExplanationReading Moral TalkExplainsTruth ∧
      ExplanatoryOrderAsymmetric Moral TalkExplainsTruth TruthExplainsTalk ∧
      ¬ QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => False, fun _ => True, fun _ => False, fun _ => False,
    fun _ => True, fun _ => False,
    fun _ h _ => h, fun h => (h () trivial).1, fun _ _ h => h.elim,
    fun _ _ => trivial, fun _ _ _ h => h, fun h => (h () trivial).1⟩

/-- Without Dreier's criterion: the sentence is robustly truth-apt although its
truth does not explain the talk. -/
theorem withoutDreierCriterionNotSustained :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt
        TalkExplainsTruth TruthExplainsTalk : Unit → Prop),
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      ¬ RobustMoralTruthIsExplanatoryReading Moral RobustlyTruthApt TruthExplainsTalk ∧
      AntirealistOrderOfExplanationReading Moral TalkExplainsTruth ∧
      ExplanatoryOrderAsymmetric Moral TalkExplainsTruth TruthExplainsTalk ∧
      ¬ QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, fun _ => False,
    fun _ _ _ => trivial, fun _ _ => ⟨trivial, trivial⟩, fun h => h () trivial trivial,
    fun _ _ => trivial, fun _ _ _ h => h, fun h => (h () trivial).2 trivial⟩

/-- Without the anti-realist order: the truth of the sentence explains the talk
(the realist order), and the sentence is robustly truth-apt. -/
theorem withoutAntirealistOrderNotSustained :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt
        TalkExplainsTruth TruthExplainsTalk : Unit → Prop),
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      RobustMoralTruthIsExplanatoryReading Moral RobustlyTruthApt TruthExplainsTalk ∧
      ¬ AntirealistOrderOfExplanationReading Moral TalkExplainsTruth ∧
      ExplanatoryOrderAsymmetric Moral TalkExplainsTruth TruthExplainsTalk ∧
      ¬ QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => True, fun _ => True,
    fun _ => False, fun _ => True,
    fun _ _ _ => trivial, fun _ _ => ⟨trivial, trivial⟩, fun _ _ _ => trivial,
    fun h => h () trivial, fun _ _ h => h.elim, fun h => (h () trivial).2 trivial⟩

/-- Without the asymmetry: each order holds of the sentence, and it is robustly
truth-apt. -/
theorem withoutAsymmetryNotSustained :
    ∃ (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt
        TalkExplainsTruth TruthExplainsTalk : Unit → Prop),
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt ∧
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse ∧
      RobustMoralTruthIsExplanatoryReading Moral RobustlyTruthApt TruthExplainsTalk ∧
      AntirealistOrderOfExplanationReading Moral TalkExplainsTruth ∧
      ¬ ExplanatoryOrderAsymmetric Moral TalkExplainsTruth TruthExplainsTalk ∧
      ¬ QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, fun _ => True,
    fun _ _ _ => trivial, fun _ _ => ⟨trivial, trivial⟩, fun _ _ _ => trivial,
    fun _ _ => trivial, fun h => h () trivial trivial trivial,
    fun h => (h () trivial).2 trivial⟩

end TruthCore.Results.Comparison.QuasiRealism.AntirealistOrderSustainsRobustTruthDeviation
