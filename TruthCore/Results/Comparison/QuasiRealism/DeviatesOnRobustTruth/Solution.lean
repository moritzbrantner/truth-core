import TruthCore.Refutations.QuasiRealism
import TruthCore.Metaethics.AnswerMap
namespace TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth
open TruthCore.English.VanRoojen
open TruthCore.Refutations.QuasiRealism
open TruthCore.Metaethics

/-- Where quasi-realism holds and there is a moral sentence (Geach's "tormenting
the cat is bad"), its answer to `Q-ROBUST-TRUTH` is not equivalent to
realism's. Were they equivalent, quasi-realism would give realism's answer, so
the moral sentence would be robustly truth-apt; but quasi-realism says it is
not. -/
theorem quasiRealismDeviatesOnRobustTruth {Sentence : Type}
    (Moral TruthApt RobustlyTruthApt : Sentence → Prop) (p : Sentence)
    (hQuasiRealism : QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    QuasiRealistRobustTruthAnswerDeviates Moral TruthApt RobustlyTruthApt := by
  intro hEquivalent
  -- INF-MATCHING-WOULD-GIVE-ROBUST-TRUTH: realism's answer would hold
  have hRealist : RealistRobustTruthAptReading Moral RobustlyTruthApt :=
    hEquivalent.mp hQuasiRealism
  -- INF-QUASI-REALISM-DEVIATES-ON-ROBUST-TRUTH: but p is moral and not robustly truth-apt
  exact (hQuasiRealism p hMoral).2 (hRealist p hMoral)

/-! ## In answer-map terms -/

/-- Any answer maps that give these answers to some question `q` do not match
there, so the quasi-realist map is a distinct rival to the realist one, and by
the collapse lemma (`MIMIC-THEORY-COLLAPSES`) it escapes collapse through this
deviation. -/
theorem quasiRealistMapIsDistinctRival {Sentence Q : Type}
    (Moral TruthApt RobustlyTruthApt : Sentence → Prop) (p : Sentence)
    (hQuasiRealism : QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p)
    (T R : AnswerMap Q) (q : Q)
    (hT : T.says q ↔ QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt)
    (hR : R.says q ↔ RealistRobustTruthAptReading Moral RobustlyTruthApt) :
    DistinctRival T R :=
  ⟨q, fun hMatches =>
    quasiRealismDeviatesOnRobustTruth Moral TruthApt RobustlyTruthApt p hQuasiRealism hMoral
      ⟨fun h => hR.mp (hMatches.2.mp (hT.mpr h)), fun h => hT.mp (hMatches.2.mpr (hR.mpr h))⟩⟩

/-! ## Countermodels -/

/-- Quasi-realism is needed: with nothing truth-apt in any sense and the moral
sentence not robustly truth-apt, both answers fail, so they are equivalent and
match. -/
theorem withoutQuasiRealismMatch :
    ∃ (Moral TruthApt RobustlyTruthApt : Unit → Prop),
      ¬ QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt ∧
      GeachMinorPremiseIsMoralReading Moral () ∧
      ¬ QuasiRealistRobustTruthAnswerDeviates Moral TruthApt RobustlyTruthApt :=
  ⟨fun _ => True, fun _ => False, fun _ => False,
    fun h => (h () trivial).1, trivial,
    fun hDeviates => hDeviates ⟨fun h => ((h () trivial).1).elim,
      fun h => (h () trivial).elim⟩⟩

/-- A moral sentence is needed: with none, both answers hold vacuously and
match. -/
theorem withoutMoralSentenceMatch :
    ∃ (Moral TruthApt RobustlyTruthApt : Unit → Prop),
      QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt ∧
      ¬ GeachMinorPremiseIsMoralReading Moral () ∧
      ¬ QuasiRealistRobustTruthAnswerDeviates Moral TruthApt RobustlyTruthApt :=
  ⟨fun _ => False, fun _ => False, fun _ => False,
    fun _ h => h.elim, id,
    fun hDeviates => hDeviates ⟨fun _ _ h => h.elim, fun _ _ h => h.elim⟩⟩

end TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth
