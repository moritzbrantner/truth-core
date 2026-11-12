module

public import TruthCore.Causality.NecessarySupportActualScope
public import TruthCore.Results.Causality.NecessarySupportCoverage.Solution
public import TruthCore.Results.Causality.ActualUnderivedEssenceEsse.Solution

@[expose] public section

namespace TruthCore.Results.Causality.NecessarySupportActualScope

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportActualScope
open TruthCore.Causality.NecessarySupportActualScope.Control
open TruthCore.Causality.NecessarySupportCoverage.Control (Tri)
open TruthCore.Causality.ActualUnderivedEssenceEsse (ActualNecessaryWellFounded)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt NecessaryBeing)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B : Type}

/-- J1 gives its selected-world instance: take the arbitrary world of J1 to be `w`. -/
theorem actualOfNoContingent (m : Profile W B) (w : W)
    (hNoCont : NoContingentConcreteSupport m w) :
    ActualNoContingentConcreteSupport m w :=
  fun c n hc hn hR => hNoCont w c n hc hn hR

/-- The join's endpoint from a necessary concretum, well-founded actual grounding,
J1 at the selected world only, coverage and excluded middle. Composes the existing
`ActualUnderivedEssenceEsse.actual_source_not_not` on the concrete subtype (an
actually existing necessary concretum with no concrete supporter existing at `w`,
double-negated) with the existing `NecessarySupportCoverage.presentSupportWF`;
coverage then excludes a concrete supporter existing at any admitted world. -/
theorem underivedFromNecessityOfActualCoverage (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w) (hWF : ActualGroundingWF m w)
    (hAct : ActualNoContingentConcreteSupport m w)
    (hCov : NecessarySupportActuallyCovered m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  have hBeing : NecessaryBeing (concreteOntic m) w := by
    obtain ⟨x, hc, he, hn⟩ := hNecessary
    exact ⟨⟨x, hc⟩, he, hn⟩
  have hNWF : ActualNecessaryWellFounded (concreteOntic m) (concreteSupport m) w :=
    Subrelation.wf (fun {_ _} h => h.2.2)
      (TruthCore.Results.Causality.NecessarySupportCoverage.presentSupportWF m w hWF)
  have hNN := TruthCore.Results.Causality.ActualUnderivedEssenceEsse.actual_source_not_not
    (concreteOntic m) (concreteSupport m) w hBeing hNWF hAct
  have hSource : ∃ n, (concreteOntic m).ExistsAt w n ∧ NecessaryAt (concreteOntic m) w n ∧
      ∀ c, (concreteOntic m).ExistsAt w c → ¬ concreteSupport m w c n := by
    cases hEM _ with
    | inl h => exact h
    | inr h => exact False.elim (hNN h)
  obtain ⟨⟨n, hc⟩, he, hn, hNo⟩ := hSource
  refine ⟨n, hc, he, hn, ?_⟩
  intro v a ha hav hg
  obtain ⟨c, hcc, hce, hcg⟩ := hCov v a n ha hc hn hav hg
  exact hNo ⟨c, hcc⟩ hce hcg

/-! ## Controls -/

/-- A relation that strictly increases a natural-number rank is well-founded. -/
theorem wf_of_rank {α : Type} (r : α → α → Prop) (f : α → Nat)
    (h : ∀ a b, r a b → f a < f b) : WellFounded r :=
  Subrelation.wf (fun {a b} hab => h a b hab) (InvImage.wf f Nat.lt_wfRel.wf)

/-- Rank of a label: `t0` lowest. -/
def rank : Tri → Nat
  | .t0 => 0
  | .t1 => 1
  | .t2 => 2

/-- Only `t2` fails to exist at `false`. -/
theorem t2_absent : ¬ ontic.ExistsAt false .t2 := fun h => nomatch h rfl

theorem absent_of_eq {a : Tri} (h : a = .t2) : ¬ ontic.ExistsAt false a := by
  subst h; exact t2_absent

/-- `t0` and `t1` exist at every world. -/
theorem exists_of_ne {v : Bool} {x : Tri} (h : x ≠ .t2) : ontic.ExistsAt v x :=
  fun hx => absurd hx h

theorem offWorldContingentControl : OffWorldContingentControl := by
  have hNec1 : NecessaryAt offWorldContingent.ontic false .t1 :=
    fun _ _ => exists_of_ne (fun h => nomatch h)
  have hNec0 : NecessaryAt offWorldContingent.ontic false .t0 :=
    fun _ _ => exists_of_ne (fun h => nomatch h)
  refine ⟨?_, ?_, ?_, ⟨.t0, trivial, exists_of_ne (fun h => nomatch h), hNec0⟩,
    ⟨.t0, trivial, exists_of_ne (fun h => nomatch h)⟩, ?_, ?_, trivial, ?_, ?_, Classical.em, ?_⟩
  · -- the instance: the only edge at `false` is `t0 → t1`
    intro c n _ _ hg
    rcases hg with ⟨-, h1, -⟩ | ⟨h, -⟩
    · show NecessaryAt offWorldContingent.ontic false c.1
      rw [h1]; exact hNec0
    · nomatch h
  · -- J1 fails: `t2` supports `t1` at `true` and is absent at `false`
    intro h
    have := h true ⟨.t2, trivial⟩ ⟨.t1, trivial⟩ (fun _ => rfl) hNec1
      (Or.inr ⟨rfl, rfl, rfl⟩)
    exact t2_absent (this false trivial)
  · exact ⟨true, .t2, .t1, trivial, trivial, fun _ => rfl, hNec1,
      Or.inr ⟨rfl, rfl, rfl⟩, false, trivial, t2_absent⟩
  · exact wf_of_rank _ (fun x => rank x.1) (by
      rintro a b (⟨-, ha, hb⟩ | ⟨h, -⟩)
      · show rank a.1 < rank b.1
        rw [ha, hb]; decide
      · nomatch h)
  · intro x _ hx hcont
    obtain ⟨_, v, _, hv⟩ := hcont
    cases x with
    | t2 => exact (t2_absent hx).elim
    | t0 => exact (hv (exists_of_ne (fun h => nomatch h))).elim
    | t1 => exact (hv (exists_of_ne (fun h => nomatch h))).elim
  · unfold ConcreteNecessaryUnionWF WellFoundedUnionNecessarySupport
    apply wf_of_rank _ (fun x => rank x.1)
    rintro a b ⟨ha, -, v, -, hg⟩
    rcases hg with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · show rank a.1 < rank b.1
      rw [show a.1 = .t0 from h1, show b.1 = .t1 from h2]; decide
    · exact (absent_of_eq h1 (ha false trivial)).elim
  · intro v a b _ _ _ _ hg
    rcases hg with ⟨-, -, hb⟩ | ⟨-, -, hb⟩ <;>
      exact ⟨.t0, trivial, exists_of_ne (fun h => nomatch h), Or.inl ⟨rfl, rfl, hb⟩⟩
  · refine ⟨.t0, trivial, exists_of_ne (fun h => nomatch h), hNec0, ?_⟩
    intro v a _ _ hg
    rcases hg with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> nomatch h

theorem lateSupportControl : LateSupportControl := by
  have hNec0 : NecessaryAt lateSupport.ontic false .t0 :=
    fun _ _ => exists_of_ne (fun h => nomatch h)
  have hNec1 : NecessaryAt lateSupport.ontic false .t1 :=
    fun _ _ => exists_of_ne (fun h => nomatch h)
  refine ⟨?_, ⟨.t0, trivial, exists_of_ne (fun h => nomatch h), hNec0⟩,
    ⟨.t0, trivial, exists_of_ne (fun h => nomatch h)⟩, ?_, ?_, trivial, ?_, Classical.em, ?_,
    ?_, ?_, ?_⟩
  · intro c n _ _ hg
    rcases hg with ⟨-, h1, -⟩ | ⟨h, -⟩
    · show NecessaryAt lateSupport.ontic false c.1
      rw [h1]; exact hNec0
    · nomatch h
  · exact wf_of_rank _ (fun x => rank x.1) (by
      rintro a b (⟨-, ha, hb⟩ | ⟨h, -⟩)
      · show rank a.1 < rank b.1
        rw [ha, hb]; decide
      · nomatch h)
  · intro x _ hx hcont
    obtain ⟨_, v, _, hv⟩ := hcont
    cases x with
    | t2 => exact (t2_absent hx).elim
    | t0 => exact (hv (exists_of_ne (fun h => nomatch h))).elim
    | t1 => exact (hv (exists_of_ne (fun h => nomatch h))).elim
  · unfold ConcreteNecessaryUnionWF WellFoundedUnionNecessarySupport
    apply wf_of_rank _ (fun x => rank x.1)
    rintro a b ⟨ha, -, v, -, hg⟩
    rcases hg with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · show rank a.1 < rank b.1
      rw [show a.1 = .t0 from h1, show b.1 = .t1 from h2]; decide
    · exact (absent_of_eq h1 (ha false trivial)).elim
  · intro v s t hs _ _ hg
    rcases hg with ⟨rfl, h1, h2⟩ | ⟨-, h1, -⟩
    · exact Or.inl ⟨rfl, h1, h2⟩
    · exact (absent_of_eq h1 (hs false trivial)).elim
  · intro h
    have := h true ⟨.t2, trivial⟩ ⟨.t0, trivial⟩ (fun _ => rfl) hNec0
      (Or.inr ⟨rfl, rfl, rfl⟩)
    exact t2_absent (this false trivial)
  · intro hCov
    obtain ⟨c, -, -, hc⟩ := hCov true .t2 .t0 trivial trivial hNec0 (fun _ => rfl)
      (Or.inr ⟨rfl, rfl, rfl⟩)
    rcases hc with ⟨-, -, h⟩ | ⟨h, -⟩ <;> nomatch h
  · rintro ⟨b, -, he, -, hu⟩
    cases b with
    | t0 => exact hu true .t2 trivial (fun _ => rfl) (Or.inr ⟨rfl, rfl, rfl⟩)
    | t1 => exact hu false .t0 trivial (exists_of_ne (fun h => nomatch h)) (Or.inl ⟨rfl, rfl, rfl⟩)
    | t2 => exact t2_absent he

/-- Both controls hold. -/
theorem controls : Controls := ⟨offWorldContingentControl, lateSupportControl⟩

end TruthCore.Results.Causality.NecessarySupportActualScope
