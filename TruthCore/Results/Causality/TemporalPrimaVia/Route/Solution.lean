import TruthCore.Causality.TemporalPrimaVia
import TruthCore.Results.Causality.TemporalActualization.Framework.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
namespace TruthCore.Results.Causality.TemporalPrimaVia.Route
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.TemporalActualization
open TruthCore.Causality.TemporalPrimaVia

/-- Under the strict horn the bridge leaves no link at any time. -/
theorem no_link_of_strict {E B T : Type} [Preorder T] (clock : E → T) (bearer : E → B)
    (C : E → E → Prop) (Link : T → B → B → Prop) (strict : StrictForward clock C)
    (hBridge : LinkOnSimultaneousEdge clock bearer C Link) (t : T) (y x : B) :
    ¬ Link t y x := by
  intro link
  obtain ⟨e, f, edge, _, _, he, hf⟩ := hBridge t y x link
  have lt := strict e f edge
  rw [he, hf] at lt
  exact lt_irrefl t lt

/-- In the simultaneous horn, the slice regress premise excludes every closed walk:
under NoBackward the walk stays at one time, and its edges are per se links. -/
theorem acyclic_of_regress {E B R T : Type} [LinearOrder T]
    (clock : E → T) (bearer : E → B) (respect : E → R) (C : E → E → Prop)
    (Moves : T → B → B → R → Prop) (Moved Actual Potency : T → B → R → Prop)
    (Link : T → B → B → Prop)
    (hNoBack : NoBackward clock C)
    (hProjection : MotionProjection clock bearer respect C Moves)
    (hLocated : LocatedMotion Moves Moved)
    (hPotential : PotentialMotion Moved Potency)
    (hActual : ActualMover Moves Actual)
    (hNotBoth : NotBoth Actual Potency)
    (hPerSe : SliceSecondMovers Moved Moves Link)
    (hRegress : ∀ t, NoInfinitePerSeMoverSeriesReading (Link t)) : EventAcyclic C := by
  have mono {a b} (p : Relation.TransGen C a b) : clock a ≤ clock b := by
    induction p with
    | single edge => exact le_of_not_gt (hNoBack _ _ edge)
    | tail _ edge ih => exact le_trans ih (le_of_not_gt (hNoBack _ _ edge))
  intro e0 cycle
  let S : E → Prop := fun a => Relation.TransGen C e0 a ∧ Relation.TransGen C a e0
  have inS0 : S e0 := ⟨cycle, cycle⟩
  have atTime {a} (ha : S a) : clock a = clock e0 :=
    le_antisymm (mono ha.2) (mono ha.1)
  have pred {a} (ha : S a) : ∃ g, S g ∧ C g a := by
    obtain ⟨g, rg, edge⟩ := Relation.TransGen.tail'_iff.mp ha.1
    have gToE0 : Relation.TransGen C g e0 :=
      (Relation.TransGen.single edge).trans ha.2
    have e0ToG : Relation.TransGen C e0 g := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp rg with rfl | p
      · exact cycle
      · exact p
    exact ⟨g, ⟨e0ToG, gToE0⟩, edge⟩
  have moves {g a} (ha : S a) (edge : C g a) :
      Moves (clock e0) (bearer g) (bearer a) (respect a) := by
    have := hProjection g a edge
    rwa [atTime ha] at this
  have movedOf {a} (ha : S a) : Moved (clock e0) (bearer a) (respect a) := by
    obtain ⟨g, _, edge⟩ := pred ha
    exact hLocated _ _ _ _ (moves ha edge)
  have step {a} (ha : S a) : ∃ g, S g ∧ Link (clock e0) (bearer g) (bearer a) := by
    obtain ⟨g, hg, edge⟩ := pred ha
    refine ⟨g, hg, hPerSe _ _ _ (respect a) ?_ (moves ha edge) ⟨_, movedOf hg⟩⟩
    intro same
    have mv := moves ha edge
    rw [same] at mv
    exact hNotBoth _ _ _ ⟨hActual _ _ _ _ mv, hPotential _ _ _ (movedOf ha)⟩
  have noneAt : ∀ x, Acc (Link (clock e0)) x → ∀ a, S a → bearer a = x → False := by
    intro x acc
    induction acc with
    | intro x _ ih =>
      intro a ha hb
      obtain ⟨g, hg, link⟩ := step ha
      rw [hb] at link
      exact ih _ link g hg rfl
  exact noneAt _ (hRegress _ _) e0 inS0 rfl

/-- Case-split the imported direction fork on the First Way at each time; the
exact `primaVia` is applied at the slice. Coverage supplies `StrictForward` in the
outcome's first horn; NoBackward rejects the third. -/
theorem route {E B R T : Type} [LinearOrder T]
    (clock : E → T) (bearer : E → B) (respect : E → R) (C : E → E → Prop)
    (Moves : T → B → B → R → Prop) (Moved Actual Potency : T → B → R → Prop)
    (Link : T → B → B → Prop)
    (hNoBack : NoBackward clock C)
    (hProjection : MotionProjection clock bearer respect C Moves)
    (hLocated : LocatedMotion Moves Moved)
    (hPotential : PotentialMotion Moved Potency)
    (hActual : ActualMover Moves Actual)
    (hNotBoth : NotBoth Actual Potency)
    (hReduction : SliceReduction Moved Moves)
    (hPerSe : SliceSecondMovers Moved Moves Link)
    (hBridge : LinkOnSimultaneousEdge clock bearer C Link)
    (hRegress : RegressIfSimultaneous clock C Link) :
    SliceRouteOutcome clock C Moved Moves := by
  have firstWay (reg : ∀ t, NoInfinitePerSeMoverSeriesReading (Link t)) (t : T)
      (sense : SomethingIsMovedReading (Moved t)) :
      FirstUnmovedMoverCannotBeLackingReading (Moved t) (Moves t) :=
    TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.primaVia
      (Moved t) (Moves t) (Potency t) (Actual t) (Link t) sense (hPotential t) (hActual t)
      (hReduction t) (hNotBoth t) (hPerSe t) (reg t)
  rcases (TruthCore.Results.Causality.TemporalActualization.Framework.framework E T clock C).1 with strict | ⟨nb, sim⟩ | back
  · have noLink := no_link_of_strict clock bearer C Link strict hBridge
    refine ⟨firstWay fun t x => Acc.intro x fun y h => (noLink t y x h).elim,
      TruthCore.Results.Causality.TemporalActualization.Framework.strict_acyclic clock C strict, Or.inl ⟨strict, ?_⟩⟩
    intro t y x r ne mv r' moved
    exact noLink t y x (hPerSe t y x r ne mv ⟨r', moved⟩)
  · have reg := hRegress sim
    exact ⟨firstWay reg,
      acyclic_of_regress clock bearer respect C Moves Moved Actual Potency Link
        hNoBack hProjection hLocated hPotential hActual hNotBoth hPerSe reg,
      Or.inr ⟨nb, sim⟩⟩
  · obtain ⟨e, f, edge, rev⟩ := back
    exact (hNoBack e f edge rev).elim
end TruthCore.Results.Causality.TemporalPrimaVia.Route
