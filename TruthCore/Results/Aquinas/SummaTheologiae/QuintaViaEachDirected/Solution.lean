import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaActsForAnEnd.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaEachDirected
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

/-- ST I q.2 a.3 co., fifth way, before the scope step: each natural body tends to
something best for it (`QuintaViaActsForAnEnd.actsForAnEnd`); natural bodies lack
cognition; and what lacks cognition tends to an end only as directed by a knower.
So each natural body is directed to something best for it by some knowing and
intelligent being. -/
theorem eachDirected {Being : Type} {End : Type}
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (RegularlyAttains Best ByChance TendsTo : Being → End → Prop)
    (Directs : Being → Being → End → Prop)
    (hLack : NaturalBodiesLackCognitionReading NaturalBody HasCognition)
    (hObs : NaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best)
    (hNotChance : RegularityIsNotByChanceReading RegularlyAttains ByChance)
    (hDich : RegularBestByChanceOrByIntentionReading RegularlyAttains Best ByChance TendsTo)
    (hArrow : NonCognitiveTendingNeedsKnowingDirectorReading HasCognition Intelligent
      TendsTo Directs) :
    EachNaturalBodyDirectedByAKnowerReading NaturalBody HasCognition Intelligent Best
      Directs := by
  -- INF-AQUINAS-ST-I-Q2-A3-QUINTA-VIA-EACH-DIRECTED: compose the first half,
  have hEnd := QuintaViaActsForAnEnd.actsForAnEnd NaturalBody RegularlyAttains Best
    ByChance TendsTo hObs hNotChance hDich
  intro x hx
  obtain ⟨e, hBest, _, hTends⟩ := hEnd x hx
  -- then the arrow and the archer, for a body without cognition
  exact ⟨e, hBest, hArrow x e (hLack x hx) hTends⟩

/-- The arrow-and-archer premise is needed (teleonomy or immanent-teleology model):
bodies without cognition regularly attain and tend to what is best, not by
chance, and nothing directs them. -/
theorem teleonomyModel :
    NaturalBodiesLackCognitionReading isBody noneP ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    ¬ NonCognitiveTendingNeedsKnowingDirectorReading noneP noneP bodyEnd noDirects ∧
    ¬ EachNaturalBodyDirectedByAKnowerReading isBody noneP noneP allEnd noDirects := by
  refine ⟨fun _ _ h => h, ⟨⟨.b0, trivial⟩, fun _ hx => ⟨(), hx, trivial⟩⟩,
    fun _ _ _ h => h, fun _ _ hReg _ => Or.inr hReg, ?_, ?_⟩
  · intro h
    obtain ⟨_, h, _⟩ := h .b0 () (fun h => h) trivial
    exact h
  · intro h
    obtain ⟨_, _, _, h, _⟩ := h .b0 trivial
    exact h

theorem twoArchersLack : NaturalBodiesLackCognitionReading isBody isDirector := by
  intro x hx
  cases x with
  | b0 => exact fun h => h
  | b1 => exact fun h => h
  | d0 => exact absurd hx (fun h => h)
  | d1 => exact absurd hx (fun h => h)

theorem twoArchersArrow :
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects := by
  intro x e _ hT
  cases x with
  | b0 => exact ⟨.d0, trivial, trivial, trivial⟩
  | b1 => exact ⟨.d1, trivial, trivial, trivial⟩
  | d0 => exact absurd hT (fun h => h)
  | d1 => exact absurd hT (fun h => h)

theorem twoArchersNoOne :
    ¬ OneIntelligentDirectsAllNaturalThingsReading isBody isDirector twoDirects := by
  intro ⟨d, hd, hAll⟩
  cases d with
  | b0 => exact hd
  | b1 => exact hd
  | d0 =>
    obtain ⟨_, h⟩ := hAll .b1 trivial
    exact h
  | d1 =>
    obtain ⟨_, h⟩ := hAll .b0 trivial
    exact h

/-- The naive scope step fails: every premise holds and each natural body is
directed by a knower, but two archers each direct one body, so no single
intelligent being directs all natural bodies. -/
theorem naiveScopeShiftFails :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects ∧
    EachNaturalBodyDirectedByAKnowerReading isBody isDirector isDirector allEnd
      twoDirects ∧
    ¬ OneIntelligentDirectsAllNaturalThingsReading isBody isDirector twoDirects := by
  have hObs : NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd :=
    ⟨⟨.b0, trivial⟩, fun _ hx => ⟨(), hx, trivial⟩⟩
  have hNC : RegularityIsNotByChanceReading bodyEnd noEnd := fun _ _ _ h => h
  have hDich : RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd :=
    fun _ _ hReg _ => Or.inr hReg
  exact ⟨twoArchersLack, hObs, hNC, hDich, twoArchersArrow,
    eachDirected isBody isDirector isDirector bodyEnd allEnd noEnd bodyEnd twoDirects
      twoArchersLack hObs hNC hDich twoArchersArrow,
    twoArchersNoOne⟩
end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaEachDirected
