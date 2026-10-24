import TruthCore.Case.Catholicism.StageOneQuintaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.Government
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaDirectorRegress
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (NaturalDirectionReducedToIntelligentImmobileDirector)

/-- The regress of directors. Let `f` direct `x` to `e`. If `f` is moved in no
respect, it is the first director. Otherwise some `g` moves it (a moved thing is
moved by a mover), `g` is not `f` (nothing is in act and in potency in the same
respect), and `g` directs `x` to `e` through `f` (q.103 a.6). If `g` is moved
too, it moves `f` only as moved, a per se link of the series; and that series
has no infinite descent (*prima via*). So, by well-founded induction, some
director of `x` to `e` is moved in no respect, and it has the design of
government, so it knows and understands (q.103 a.6). -/
theorem directorRegress {Being : Type} {Respect : Type} {End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved)
    (hEM : ExcludedMiddle)
    (hThrough : DirectionThroughIntermediariesReading MovesIn Directs)
    (hDesign : UnmovedDirectorHasTheDesignReading MovedIn HasCognition Intelligent Directs) :
    NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody HasCognition
      Intelligent Directs := by
  intro d x e _ hd
  -- INF-AQUINAS-Q103-DIRECTOR-REGRESS: induction along the per se series
  have hTop : ∀ f, Directs f x e → ∃ h, Directs h x e ∧ ∀ r, ¬ MovedIn h r := by
    intro f
    induction hRegress f with
    | intro f _ ih =>
      intro hf
      cases hEM (∃ r, MovedIn f r) with
      | inr hUnmoved => exact ⟨f, hf, fun r hr => hUnmoved ⟨r, hr⟩⟩
      | inl hMoved =>
        obtain ⟨r, hr⟩ := hMoved
        obtain ⟨g, hg⟩ := hReduction f r hr
        have hOther : g ≠ f := by
          intro hSame
          subst hSame
          exact hNotBoth g r ⟨hAct g g r hg, hPotency g r hr⟩
        have hgDirects : Directs g x e := hThrough g f x e r hf hg hOther
        cases hEM (∃ r', MovedIn g r') with
        | inr hUnmoved => exact ⟨g, hgDirects, fun r' hr' => hUnmoved ⟨r', hr'⟩⟩
        | inl hgMoved => exact ih g (hPerSe g f r hOther hg hgMoved) hgDirects
  obtain ⟨h, hh, hUnmoved⟩ := hTop d hd
  -- INF-AQUINAS-Q103-FIRST-DIRECTOR-HAS-DESIGN
  obtain ⟨hCognition, hIntelligent⟩ := hDesign h x e hh hUnmoved
  exact ⟨h, hCognition, hIntelligent, hUnmoved, hh⟩

/-- The design reading (q.103 a.6) is needed: one natural body that directs
itself, moved by nothing and lacking intellect. Every other premise holds, but
no intelligent director exists. -/
theorem withoutDesignNoIntelligentDirector :
    ∃ (MovedIn : Unit → Unit → Prop) (MovesIn : Unit → Unit → Unit → Prop)
      (InPotency InAct : Unit → Unit → Prop) (MovesAsMoved : Unit → Unit → Prop)
      (NaturalBody HasCognition Intelligent : Unit → Prop)
      (Directs : Unit → Unit → Unit → Prop),
      MovedOnlyAsInPotencyReading MovedIn InPotency ∧
      MovesOnlyAsInActReading MovesIn InAct ∧
      NotActAndPotencyInSameRespectReading InAct InPotency ∧
      ReducedOnlyByAMoverReading MovedIn MovesIn ∧
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved ∧
      NoInfinitePerSeMoverSeriesReading MovesAsMoved ∧
      DirectionThroughIntermediariesReading MovesIn Directs ∧
      ¬ UnmovedDirectorHasTheDesignReading MovedIn HasCognition Intelligent Directs ∧
      ¬ NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody HasCognition
        Intelligent Directs :=
  ⟨fun _ _ => False, fun _ _ _ => False, fun _ _ => False, fun _ _ => False,
    fun _ _ => False, fun _ => True, fun _ => False, fun _ => False, fun _ _ _ => True,
    fun _ _ h => h.elim, fun _ _ _ h => h.elim, fun _ _ h => h.1.elim,
    fun _ _ h => h.elim, fun _ _ _ _ h => h.elim,
    fun x => Acc.intro x (fun _ h => h.elim), fun _ _ _ _ _ _ h => h.elim,
    fun h => (h () () () trivial (fun _ hr => hr)).1.elim,
    fun h => by
      obtain ⟨_, hCognition, _⟩ := h () () () trivial trivial
      exact hCognition⟩

end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaDirectorRegress
