import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaEachDirected.Solution
import TruthCore.Case.Catholicism.StageOneQuintaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaOneGovernor
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover IsFirstUnmovedMover
  OneIntelligentFirstMoverGovernsNature NaturalDirectionReducedToIntelligentImmobileDirector
  DirectingIsMoving)

/-- ST I q.2 a.3, fifth way with ad 2: the scope step. Each natural body is
directed by some knower (`QuintaViaEachDirected.eachDirected`). By the open
bridge on which ad 2 bears, its direction is reduced to an intelligent director
moved by none; by the open bridge that directing is moving, that director is a
first mover moved by none. There is at most one
such (stage 1, `AtMostOneFirstUnmovedMover`). So one intelligent first mover
directs every natural body. -/
theorem oneGovernor {Being : Type} {Respect : Type} {End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (RegularlyAttains Best ByChance TendsTo : Being → End → Prop)
    (Directs : Being → Being → End → Prop)
    (hLack : NaturalBodiesLackCognitionReading NaturalBody HasCognition)
    (hObs : NaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best)
    (hNotChance : RegularityIsNotByChanceReading RegularlyAttains ByChance)
    (hDich : RegularBestByChanceOrByIntentionReading RegularlyAttains Best ByChance TendsTo)
    (hArrow : NonCognitiveTendingNeedsKnowingDirectorReading HasCognition Intelligent
      TendsTo Directs)
    (hReduce : NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody
      HasCognition Intelligent Directs)
    (hMoving : DirectingIsMoving MovesIn Directs)
    (hOne : AtMostOneFirstUnmovedMover MovedIn MovesIn) :
    OneIntelligentFirstMoverGovernsNature MovedIn MovesIn NaturalBody Intelligent
      Directs := by
  -- INF-AQUINAS-ST-I-Q2-A3-QUINTA-VIA-ONE-GOVERNOR: each body has a director,
  have hEach := QuintaViaEachDirected.eachDirected NaturalBody HasCognition Intelligent
    RegularlyAttains Best ByChance TendsTo Directs hLack hObs hNotChance hDich hArrow
  -- whose direction reduces to an intelligent first mover moved by none,
  have hFirst : ∀ x, NaturalBody x → ∃ f e, Intelligent f ∧
      IsFirstUnmovedMover MovedIn MovesIn f ∧ Directs f x e := by
    intro x hx
    obtain ⟨e, _, d, _, _, hd⟩ := hEach x hx
    obtain ⟨f, _, hfI, hfU, hf⟩ := hReduce d x e hx hd
    obtain ⟨r, hr⟩ := hMoving f x e hf
    exact ⟨f, e, hfI, ⟨⟨x, r, hr⟩, hfU⟩, hf⟩
  -- there is a natural body, so such a first mover f,
  obtain ⟨x0, hx0⟩ := hObs.1
  obtain ⟨f, _, hfI, hfF, _⟩ := hFirst x0 hx0
  refine ⟨f, hfF, hfI, ?_⟩
  -- and by uniqueness it directs every natural body
  intro x hx
  obtain ⟨g, e, _, hgF, hg⟩ := hFirst x hx
  have hgf : g = f := hOne g f hgF hfF
  exact ⟨e, hgf ▸ hg⟩

/-- The derived statement entails the *quinta via*'s literal conclusion. -/
theorem entailsQuintaViaConclusion {Being : Type} {Respect : Type} {End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (NaturalBody Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop)
    (h : OneIntelligentFirstMoverGovernsNature MovedIn MovesIn NaturalBody Intelligent
      Directs) :
    OneIntelligentDirectsAllNaturalThingsReading NaturalBody Intelligent Directs := by
  obtain ⟨d, _, hI, hAll⟩ := h
  exact ⟨d, hI, hAll⟩

private theorem obsHolds : NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd :=
  ⟨⟨.b0, trivial⟩, fun _ hx => ⟨(), hx, trivial⟩⟩

private theorem dichHolds :
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd :=
  fun _ _ hReg _ => Or.inr hReg

/-- In the two-archers model, whoever directs is a director. -/
private theorem twoDirectsDirector (d x : W) (e : Unit) (h : twoDirects d x e) :
    isDirector d := by
  cases d with
  | b0 => exact h
  | b1 => exact h
  | d0 => trivial
  | d1 => trivial

/-- The two archers move nothing as unmoved movers when directors are moved. -/
private theorem noFirstWhenDirectorsMoved (f : W)
    (hf : IsFirstUnmovedMover directorsMoved twoDirects f) : False := by
  obtain ⟨⟨x, r, hm⟩, hu⟩ := hf
  cases f with
  | b0 => exact hm
  | b1 => exact hm
  | d0 => exact hu () trivial
  | d1 => exact hu () trivial

/-- The reduction bridge is needed: two archers each direct one body, and
the archers are themselves moved. Every other premise holds (uniqueness
vacuously); there is no first director and no one governor. -/
theorem withoutReduction :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects ∧
    DirectingIsMoving twoDirects twoDirects ∧
    AtMostOneFirstUnmovedMover directorsMoved twoDirects ∧
    ¬ NaturalDirectionReducedToIntelligentImmobileDirector directorsMoved isBody isDirector
      isDirector twoDirects ∧
    ¬ OneIntelligentFirstMoverGovernsNature directorsMoved twoDirects isBody isDirector
      twoDirects := by
  refine ⟨QuintaViaEachDirected.twoArchersLack, obsHolds, fun _ _ _ h => h, dichHolds,
    QuintaViaEachDirected.twoArchersArrow, fun _ _ e h => ⟨e, h⟩,
    fun f _ hf _ => (noFirstWhenDirectorsMoved f hf).elim, ?_, ?_⟩
  · intro h
    obtain ⟨f, hfC, _, hfU, _⟩ := h .d0 .b0 () trivial trivial
    cases f with
    | b0 => exact hfC
    | b1 => exact hfC
    | d0 => exact hfU () trivial
    | d1 => exact hfU () trivial
  · intro ⟨f, hfF, _, _⟩
    exact noFirstWhenDirectorsMoved f hfF

/-- Directing-is-moving is needed: the two archers are moved by none and direct,
but move nothing, so they are not first movers and uniqueness does not apply. -/
theorem withoutDirectingIsMoving :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects ∧
    NaturalDirectionReducedToIntelligentImmobileDirector nothingMoved isBody isDirector
      isDirector twoDirects ∧
    AtMostOneFirstUnmovedMover nothingMoved noMoves ∧
    ¬ DirectingIsMoving noMoves twoDirects ∧
    ¬ OneIntelligentFirstMoverGovernsNature nothingMoved noMoves isBody isDirector
      twoDirects := by
  refine ⟨QuintaViaEachDirected.twoArchersLack, obsHolds, fun _ _ _ h => h, dichHolds,
    QuintaViaEachDirected.twoArchersArrow, ?_, ?_, ?_, ?_⟩
  · intro d x e _ hd
    have hD := twoDirectsDirector d x e hd
    exact ⟨d, hD, hD, fun _ h => h, hd⟩
  · intro f _ hf _
    obtain ⟨⟨_, _, h⟩, _⟩ := hf
    exact h.elim
  · intro h
    obtain ⟨_, h⟩ := h .d0 .b0 () trivial
    exact h
  · intro ⟨_, ⟨⟨_, _, h⟩, _⟩, _, _⟩
    exact h

/-- The stage-1 uniqueness premise is needed: both archers are moved by none and
move what they direct, so there are two first movers, each directing one body. -/
theorem withoutUniqueness :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects ∧
    NaturalDirectionReducedToIntelligentImmobileDirector nothingMoved isBody isDirector
      isDirector twoDirects ∧
    DirectingIsMoving twoDirects twoDirects ∧
    ¬ AtMostOneFirstUnmovedMover nothingMoved twoDirects ∧
    ¬ OneIntelligentFirstMoverGovernsNature nothingMoved twoDirects isBody isDirector
      twoDirects := by
  refine ⟨QuintaViaEachDirected.twoArchersLack, obsHolds, fun _ _ _ h => h, dichHolds,
    QuintaViaEachDirected.twoArchersArrow, ?_, fun _ _ e h => ⟨e, h⟩, ?_, ?_⟩
  · intro d x e _ hd
    have hD := twoDirectsDirector d x e hd
    exact ⟨d, hD, hD, fun _ h => h, hd⟩
  · intro h
    have hEq : W.d0 = W.d1 :=
      h .d0 .d1 ⟨⟨.b0, (), trivial⟩, fun _ h => h⟩ ⟨⟨.b1, (), trivial⟩, fun _ h => h⟩
    exact W.noConfusion hEq
  · intro ⟨d, _, hI, hAll⟩
    exact QuintaViaEachDirected.twoArchersNoOne ⟨d, hI, hAll⟩

/-- All premises are jointly satisfiable, non-vacuously: one governor `d0`, moved
by none, directs and moves both natural bodies. -/
theorem premisesJointlySatisfiable :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      oneDirects ∧
    NaturalDirectionReducedToIntelligentImmobileDirector nothingMoved isBody isDirector
      isDirector oneDirects ∧
    DirectingIsMoving oneDirects oneDirects ∧
    AtMostOneFirstUnmovedMover nothingMoved oneDirects := by
  have isD0 : ∀ d x e, oneDirects d x e → d = W.d0 := by
    intro d x e h
    cases d with
    | b0 => exact h.elim
    | b1 => exact h.elim
    | d0 => rfl
    | d1 => exact h.elim
  refine ⟨QuintaViaEachDirected.twoArchersLack, obsHolds, fun _ _ _ h => h, dichHolds,
    ?_, ?_, fun _ _ e h => ⟨e, h⟩, ?_⟩
  · intro x e _ hT
    exact ⟨.d0, trivial, trivial, hT⟩
  · intro d x e _ hd
    have hEq := isD0 d x e hd
    subst hEq
    exact ⟨.d0, trivial, trivial, fun _ h => h, hd⟩
  · intro f g hf hg
    obtain ⟨⟨x, r, hfm⟩, _⟩ := hf
    obtain ⟨⟨y, s, hgm⟩, _⟩ := hg
    rw [isD0 f x r hfm, isD0 g y s hgm]
end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaOneGovernor
