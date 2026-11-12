module

public import TruthCore.Causality.NecessarySupportCoverage
public import TruthCore.Causality.NecessaryConcreteRouteBridge
public import TruthCore.Results.Causality.SpineRivalsRootEsse.Solution

@[expose] public section

namespace TruthCore.Results.Causality.NecessarySupportCoverage

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryConcreteRouteBridge (necessaryActualRootOfGrounded)
open TruthCore.Causality.SpineRivalsRootEsse
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportCoverage.Control
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B : Type}

/-- Well-founded present concrete grounding at `w` makes the existing
present-support relation on the concrete subtype well-founded: a present
supporter exists at `w`, so its accessibility comes from the actual relation. -/
theorem presentSupportWF (m : Profile W B) (w : W) (hWF : ActualGroundingWF m w) :
    WellFoundedPresentEsseSupport (concreteOntic m) (concreteSupport m) w := by
  have hActual : ∀ a : {x // ActualConcrete m w x},
      Acc (PresentEsseSupport (concreteOntic m) (concreteSupport m) w) ⟨a.1, a.2.1⟩ := by
    intro a
    induction a using hWF.induction with
    | _ a ih =>
      constructor
      intro s hs
      exact ih ⟨s.1, s.2, hs.1⟩ hs.2
  constructor
  intro t
  constructor
  intro s hs
  exact hActual ⟨s.1, s.2, hs.1⟩

/-- J2 derived. Reflexive access at `w`, well-founded present concrete grounding
at `w` (both already premises of the join) and the existing one-way no-novel-edge
condition on the concrete subtype give a well-founded cross-world union of support
among necessary concreta. Composes `union_wellFounded_of_actual_wellFounded`. -/
theorem unionWFOfNoNovel (m : Profile W B) (w : W)
    (hRef : ActualReflexive m.ontic w) (hWF : ActualGroundingWF m w)
    (hNoNovel : NoNovelNecessarySupport (concreteOntic m) (concreteSupport m) w) :
    ConcreteNecessaryUnionWF m w :=
  union_wellFounded_of_actual_wellFounded (concreteOntic m) (concreteSupport m) w
    hRef hNoNovel (presentSupportWF m w hWF)

/-- The mutual-support rival is excluded by reflexive access at `w`, well-founded
present grounding at `w` and the one-way no-novel-edge condition. -/
theorem mutualSupportExcluded (m : Profile W B) (w : W)
    (hRef : ActualReflexive m.ontic w) (hWF : ActualGroundingWF m w)
    (hNoNovel : NoNovelNecessarySupport (concreteOntic m) (concreteSupport m) w) :
    NoNecessaryConcretaMutualSupport m w := fun h =>
  TruthCore.Results.Causality.SpineRivalsRootEsse.mutualSupport_excludes m w h
    (unionWFOfNoNovel m w hRef hWF hNoNovel)

/-- The join's endpoint without J1, J2 or reflexive access. The actual necessary
root (`necessaryActualRootOfGrounded`) has no concrete ground at `w`; coverage
transfers that to every admitted world. The witness is that root itself. -/
theorem underivedOfCoverage (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hCov : NecessarySupportActuallyCovered m w) :
    NecessaryConcreteUnderivedAt m w := by
  obtain ⟨x, ⟨⟨hc, he⟩, hroot⟩, hn⟩ := necessaryActualRootOfGrounded m w hPop hWF hDep hEM
  refine ⟨x, hc, he, hn, ?_⟩
  intro v a ha hav hg
  obtain ⟨c, hcc, hce, hcg⟩ := hCov v a x ha hc hn hav hg
  exact hroot c ⟨hcc, hce, hcg⟩

/-- The stage-one form of the join without J2 or reflexive access: from a
necessary concretum, well-founded present grounding at `w`, J1 and coverage.
Descend present grounding among actual necessary concreta. A supporter of such a
concretum at any admitted world yields, by coverage, a present concrete supporter
at `w`, which J1 (used only at `w`) makes necessary and which is lower; so a minimal
one has no existing concrete supporter at any admitted world. Constructive core,
then excluded middle. The witness may differ from the given one. -/
theorem underivedFromNecessityOfCoverage (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w) (hWF : ActualGroundingWF m w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hCov : NecessarySupportActuallyCovered m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  have hNN : ¬¬ NecessaryConcreteUnderivedAt m w := by
    intro hNone
    obtain ⟨b, hc, he, hn⟩ := hNecessary
    have walk : ∀ a : {x // ActualConcrete m w x}, NecessaryAt m.ontic w a.1 → False := by
      intro a
      induction a using hWF.induction with
      | _ a ih =>
        intro hna
        apply hNone
        refine ⟨a.1, a.2.1, a.2.2, hna, ?_⟩
        intro v s hs hsv hg
        obtain ⟨c, hcc, hce, hcg⟩ := hCov v s a.1 hs a.2.1 hna hsv hg
        have hcn : NecessaryAt m.ontic w c :=
          hNoCont w ⟨c, hcc⟩ ⟨a.1, a.2.1⟩ hce hna hcg
        exact ih ⟨c, hcc, hce⟩ hcg hcn
    exact walk ⟨b, hc, he⟩ hn
  rcases hEM (NecessaryConcreteUnderivedAt m w) with h | h
  · exact h
  · exact (hNN h).elim

/-- Coverage is implied by reflexive access, J1 (no contingent concrete support)
and the one-way no-novel-edge condition: the supporter elsewhere is necessary, so
it exists at `w`, and its edge already occurs at `w`. -/
theorem coverageOfNoContingentNoNovel (m : Profile W B) (w : W)
    (hRef : ActualReflexive m.ontic w) (hNoCont : NoContingentConcreteSupport m w)
    (hNoNovel : NoNovelNecessarySupport (concreteOntic m) (concreteSupport m) w) :
    NecessarySupportActuallyCovered m w := by
  intro v a b ha hb hn hav hg
  have hna : NecessaryAt (concreteOntic m) w ⟨a, ha⟩ :=
    hNoCont v ⟨a, ha⟩ ⟨b, hb⟩ hav hn hg
  exact ⟨a, ha, hna w hRef, hNoNovel v ⟨a, ha⟩ ⟨b, hb⟩ hna hn hav hg⟩

/-- Coverage is implied by the existing same-supporter presence premise: the
supporter found elsewhere is itself present and supporting at `w`. -/
theorem coverageOfSupportIsPresent (m : Profile W B) (w : W)
    (hPresent : TruthCore.Causality.UnderivedRootRoute.NecessarySupportIsPresent m w) :
    NecessarySupportActuallyCovered m w := by
  intro v a b ha _ hn hav hg
  obtain ⟨haw, hgw⟩ := hPresent v a b hn hav hg
  exact ⟨a, ha, haw, hgw⟩

/-! ## Controls -/

/-- A relation that strictly increases a natural-number rank is well-founded. -/
theorem wf_of_rank {α : Type} (r : α → α → Prop) (f : α → Nat)
    (h : ∀ a b, r a b → f a < f b) : WellFounded r :=
  Subrelation.wf (fun {a b} hab => h a b hab) (InvImage.wf f Nat.lt_wfRel.wf)

/-- A relation in which some element of a set `P` exists and every element of
`P` has an `r`-predecessor in `P` is not well-founded. -/
theorem not_wf_of_pred {α : Type} (r : α → α → Prop) (P : α → Prop)
    (h : ∀ x, P x → ∃ y, P y ∧ r y x) (x₀ : α) (h₀ : P x₀) : ¬ WellFounded r := by
  intro hWF
  have key : ∀ x, P x → False := by
    intro x
    induction x using hWF.induction with
    | _ x ih =>
      intro hx
      obtain ⟨y, hy, hyx⟩ := h x hx
      exact ih y hyx hy
  exact key x₀ h₀

/-- Rank for the rotating triangle at world `v`: `0` for `v`'s own label. -/
def triangleRank : Tri → Tri → Nat
  | .t0, .t0 => 0
  | .t1, .t1 => 0
  | .t2, .t2 => 0
  | _, _ => 1

/-- Rank for the rooted pair at world `v`, following that world's chain. -/
def pairRank : Bool → Tri → Nat
  | false, .t0 => 0
  | false, .t1 => 1
  | false, .t2 => 2
  | true, .t0 => 0
  | true, .t2 => 1
  | true, .t1 => 2

theorem rotatingTriangleSurvives : RotatingTriangleSurvives := by
  have hRank : ∀ v a b, rotatingTriangle.grounds v a b →
      triangleRank v a < triangleRank v b := by
    intro v a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
  have hEvery : EveryWorldGroundingWF rotatingTriangle := fun v =>
    wf_of_rank _ (fun x => triangleRank v x.1) (fun a b h => hRank v a.1 b.1 h)
  have hPred : ∀ b : Tri, ∃ a : Tri, rotatingTriangle.grounds a a b := by
    intro b
    cases b
    · exact ⟨.t2, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
    · exact ⟨.t0, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨.t1, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  have hUnion : ¬ ConcreteNecessaryUnionWF rotatingTriangle .t0 := by
    refine not_wf_of_pred _ (fun _ => True) ?_ ⟨.t0, trivial⟩ trivial
    intro x _
    obtain ⟨a, ha⟩ := hPred x.1
    exact ⟨⟨a, trivial⟩, trivial, fun _ _ => trivial, fun _ _ => trivial, a, trivial, ha⟩
  refine ⟨?_, hEvery, ⟨.t0, trivial, trivial⟩, hEvery .t0, ?_, trivial,
    fun _ _ _ _ _ _ _ _ => trivial, Classical.em, hUnion, ?_, ?_⟩
  · rintro ⟨a, b, v, u, -, -, -, -, -, hab, -, hba⟩
    rcases hab with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hba with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;>
      first | (cases h1; done) | cases h2
  · intro x _ _ hcont
    obtain ⟨_, v, _, hv⟩ := hcont
    exact (hv trivial).elim
  · rintro ⟨b, -, -, -, hu⟩
    obtain ⟨a, ha⟩ := hPred b
    exact hu a a trivial trivial ha
  · intro hCov
    obtain ⟨c, -, -, hc⟩ := hCov .t2 .t2 .t0 trivial trivial (fun _ _ => trivial) trivial
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    rcases hc with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> nomatch h

theorem rootedPairCompatible : RootedPairCompatible := by
  have hRank : ∀ v a b, rootedPair.grounds v a b → pairRank v a < pairRank v b := by
    intro v a b h
    rcases h with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> decide
  have hEvery : EveryWorldGroundingWF rootedPair := fun v =>
    wf_of_rank _ (fun x => pairRank v x.1) (fun a b h => hRank v a.1 b.1 h)
  have hMutual : NecessaryConcretaMutualSupport rootedPair false :=
    ⟨.t1, .t2, false, true, trivial, trivial, fun _ _ => trivial, fun _ _ => trivial,
      trivial, Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, trivial, Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  refine ⟨hMutual, hEvery, ⟨.t0, trivial, trivial⟩, hEvery false, ?_, trivial,
    fun _ _ _ _ _ _ _ _ => trivial, ?_, Classical.em,
    TruthCore.Results.Causality.SpineRivalsRootEsse.mutualSupport_excludes _ _ hMutual, ?_, ?_, ?_⟩
  · intro x _ _ hcont
    obtain ⟨_, v, _, hv⟩ := hcont
    exact (hv trivial).elim
  · intro v a b _ _ _ _ hg
    rcases hg with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨.t0, trivial, trivial, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨.t1, trivial, trivial, Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · exact ⟨.t1, trivial, trivial, Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · exact ⟨.t0, trivial, trivial, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  · intro h
    have hEdge : rootedPair.grounds false .t2 .t1 :=
      h true ⟨.t2, trivial⟩ ⟨.t1, trivial⟩ (fun _ _ => trivial) (fun _ _ => trivial)
        trivial (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)
    rcases hEdge with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨h1, -⟩ <;> nomatch h1
  · intro h
    obtain ⟨-, hEdge⟩ := h true .t2 .t1 (fun _ _ => trivial) trivial
      (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)
    rcases hEdge with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨h1, -⟩ <;> nomatch h1
  · refine ⟨.t0, trivial, trivial, fun _ _ => trivial, ?_⟩
    intro v a _ _ hg
    rcases hg with ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ <;> nomatch h

theorem uncoveredEdgeControl : UncoveredEdgeControl := by
  refine ⟨⟨false, trivial, trivial⟩, ?_, ?_, trivial, fun _ _ _ _ _ _ _ _ => trivial, ?_,
    Classical.em, ?_, ?_, ?_⟩
  · exact wf_of_rank _ (fun _ => 0) (fun a b h => by obtain ⟨h1, -⟩ := h; nomatch h1)
  · intro x _ _ hcont
    obtain ⟨_, v, _, hv⟩ := hcont
    exact (hv trivial).elim
  · unfold ConcreteNecessaryUnionWF WellFoundedUnionNecessarySupport
    apply wf_of_rank _ (fun x => x.1.toNat)
    rintro a b ⟨-, -, v, -, -, ha, hb⟩
    show a.1.toNat < b.1.toNat
    rw [ha, hb]
    decide
  · intro hCov
    obtain ⟨c, -, -, h1, -⟩ := hCov true false true trivial trivial (fun _ _ => trivial) trivial
      ⟨rfl, rfl, rfl⟩
    nomatch h1
  · intro h
    obtain ⟨h1, -⟩ := h true ⟨false, trivial⟩ ⟨true, trivial⟩ (fun _ _ => trivial)
      (fun _ _ => trivial) trivial ⟨rfl, rfl, rfl⟩
    nomatch h1
  · refine ⟨false, trivial, trivial, fun _ _ => trivial, ?_⟩
    intro v a _ _ hg
    obtain ⟨-, -, h1⟩ := hg
    nomatch h1

/-- All three controls hold. -/
theorem controls : Controls :=
  ⟨rotatingTriangleSurvives, rootedPairCompatible, uncoveredEdgeControl⟩

end TruthCore.Results.Causality.NecessarySupportCoverage
