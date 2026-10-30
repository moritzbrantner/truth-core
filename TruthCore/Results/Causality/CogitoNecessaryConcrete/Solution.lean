import TruthCore.Causality.CogitoNecessaryConcrete
import TruthCore.Results.Logic.CogitoSubject.Solution

namespace TruthCore.Results.Causality.CogitoNecessaryConcrete

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic (ExcludedMiddle)

/-- Thinker-local fork: an occurring thought with a concrete bearer existing at
`w`, accessible for actual concrete grounding, has either a necessary concrete
ground-ancestor or a contingent concrete root among its ground-ancestors.

Proof: take the bearer from `thinkingSubjectOfThought` (#532) and descend
along actual concrete grounds by `Acc` induction. At each ancestor, excluded
middle decides whether it has an actual concrete ground (descend), else whether
it is contingent (a root: second horn), else it exists at every accessible
world (first horn). -/
theorem ancestryRootForkWithRoot {W B Episode : Type}
    (m : Profile W B) (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkerGroundingAccessible m Occurs Bears w)
    (hEM : ExcludedMiddle) :
    (NecessaryConcreteRootAncestorOfThinker m Occurs Bears w ∨
      ContingentRootAncestorOfThinker m Occurs Bears w) := by
  obtain ⟨b, e, he, hb⟩ :=
    TruthCore.Results.Logic.CogitoSubject.thinkingSubjectOfThought Occurs Bears hOccurs hBearer
  have walk : ∀ x, Acc (ActualConcreteGround m w) x → GroundAncestor m w x b →
      m.concrete x → m.ontic.ExistsAt w x → (NecessaryConcreteRootAncestorOfThinker m Occurs Bears w ∨
      ContingentRootAncestorOfThinker m Occurs Bears w) := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hanc hc hex
      rcases hEM (∃ y, ActualConcreteGround m w y x) with ⟨y, hy⟩ | hnone
      · exact ih y hy (Relation.ReflTransGen.head hy hanc) hy.1 hy.2.1
      · rcases hEM (ContingentAt m.ontic w x) with hcont | hncont
        · exact Or.inr ⟨b, e, x, he, hb, hanc, hc, hex, hcont, fun y hy => hnone ⟨y, hy⟩⟩
        · refine Or.inl ⟨b, e, x, he, hb, hanc, hc, hex, ?_, fun y hy => hnone ⟨y, hy⟩⟩
          intro v hv
          rcases hEM (m.ontic.ExistsAt v x) with h | h
          · exact h
          · exact (hncont ⟨hex, v, hv, h⟩).elim
  exact walk b (hAcc b e he hb) Relation.ReflTransGen.refl (hConcrete b e he hb)
    (hExists b e he hb)

/-- Original frozen fork, projected from the same descent with its minimality
fact retained by `ancestryRootForkWithRoot`. -/
theorem ancestryRootFork {W B Episode : Type}
    (m : Profile W B) (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkerGroundingAccessible m Occurs Bears w)
    (hEM : ExcludedMiddle) :
    ThinkerAncestryRootFork m Occurs Bears w := by
  rcases ancestryRootForkWithRoot m Occurs Bears w hOccurs hBearer hConcrete hExists hAcc hEM with
    ⟨b, e, x, he, hb, ha, hc, hx, hn, _⟩ | h
  · exact Or.inl ⟨b, e, x, he, hb, ha, hc, hx, hn⟩
  · exact Or.inr h

/-- The same minimal ancestor is necessary: the original ancestry-grounding
premise excludes a contingent minimal ancestor. No necessary→underived axiom. -/
theorem necessaryConcreteRootAncestor {W B Episode : Type}
    (m : Profile W B) (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkerGroundingAccessible m Occurs Bears w)
    (hGrounded : ThinkerAncestryGrounded m Occurs Bears w)
    (hEM : ExcludedMiddle) :
    NecessaryConcreteRootAncestorOfThinker m Occurs Bears w := by
  rcases ancestryRootForkWithRoot m Occurs Bears w hOccurs hBearer hConcrete hExists hAcc hEM with
    h | ⟨b, e, x, he, hb, ha, hc, hx, ht, hroot⟩
  · exact h
  · obtain ⟨y, hy⟩ := hGrounded b e x he hb ha hc hx ht
    exact (hroot y hy).elim

/-- Adding the thinker-local anti-brute-root principle closes the second horn
of `ancestryRootFork`: some bearer of an occurring thought has a necessary
concrete ground-ancestor. -/
theorem necessaryConcreteAncestor {W B Episode : Type}
    (m : Profile W B) (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkerGroundingAccessible m Occurs Bears w)
    (hGrounded : ThinkerAncestryGrounded m Occurs Bears w)
    (hEM : ExcludedMiddle) :
    NecessaryConcreteAncestorOfThinker m Occurs Bears w := by
  obtain ⟨b, e, x, he, hb, ha, hc, hx, hn, _⟩ :=
    necessaryConcreteRootAncestor m Occurs Bears w
      hOccurs hBearer hConcrete hExists hAcc hGrounded hEM
  exact ⟨b, e, x, he, hb, ha, hc, hx, hn⟩

/-! ## Controls -/

theorem globalImpliesLocal : GlobalPremisesImplyThinkerLocal := by
  intro W B Episode m Occurs Bears w
  refine ⟨?_, ?_⟩
  · intro hWF b _ _ _
    exact Subrelation.accessible (fun h => h.2.2) (hWF.apply b)
  · intro hDep _ _ x _ _ _ hc hex hcont
    obtain ⟨y, hyc, hye, hyg⟩ := hDep x hc hex hcont
    exact ⟨y, hyc, hye, hyg⟩

/-- In the strictness model the only ground-ancestor of the thinker is the
thinker itself, since nothing grounds the thinker. -/
theorem strict_ancestor_eq {x : Cand}
    (h : GroundAncestor strictProfile true x Cand.thinker) : x = Cand.thinker := by
  cases h with
  | refl => rfl
  | tail _ hr =>
    rename_i b _
    cases b <;> exact False.elim hr.2.2

theorem strict_left_right_not_acc :
    ∀ x, Acc (strictProfile.grounds true) x → x = Cand.left ∨ x = Cand.right → False := by
  intro x hx
  induction hx with
  | intro x _ ih =>
    intro hx
    rcases hx with rfl | rfl
    · exact ih Cand.right trivial (Or.inr rfl)
    · exact ih Cand.left trivial (Or.inl rfl)

theorem strictlyWeaker : StrictlyWeakerModel := by
  refine ⟨⟨(), trivial⟩, fun _ _ => ⟨Cand.thinker, trivial⟩, fun _ _ _ _ => trivial, ?_,
    ?_, ?_, ?_, fun _ _ => trivial, ?_, ?_, ?_⟩
  · intro b _ _ hb
    cases b with
    | thinker => trivial
    | left => exact hb.elim
    | right => exact hb.elim
    | brute => exact hb.elim
  · intro b _ _ hb
    cases b with
    | thinker => exact Acc.intro _ fun y hy => by cases y <;> exact False.elim hy.2.2
    | left => exact hb.elim
    | right => exact hb.elim
    | brute => exact hb.elim
  · intro b _ x _ hb hanc _ _ hcont
    cases b with
    | thinker =>
      have hx := strict_ancestor_eq hanc
      subst hx
      obtain ⟨_, v, _, hv⟩ := hcont
      exact (hv trivial).elim
    | left => exact hb.elim
    | right => exact hb.elim
    | brute => exact hb.elim
  · exact ⟨Cand.thinker, (), Cand.thinker, trivial, trivial, Relation.ReflTransGen.refl,
      trivial, trivial, fun _ _ => trivial⟩
  · intro ⟨_, v, _, hv⟩
    exact hv trivial
  · intro hWF
    exact strict_left_right_not_acc Cand.left (hWF.apply _) (Or.inl rfl)
  · intro hDep
    have hcont : ContingentAt strictProfile.ontic true Cand.brute :=
      ⟨rfl, false, trivial, fun h => Bool.noConfusion h⟩
    obtain ⟨y, _, _, hy⟩ := hDep Cand.brute trivial rfl hcont
    cases y <;> exact False.elim hy

theorem cycle_not_acc :
    ∀ x, Acc (ActualConcreteGround cycleProfile true) x → False := by
  intro x hx
  induction hx with
  | intro x _ ih =>
    cases x with
    | false => exact ih true ⟨trivial, rfl, Bool.noConfusion⟩
    | true => exact ih false ⟨trivial, rfl, Bool.noConfusion⟩

theorem ancestryControls : CogitoAncestryControls := by
  refine ⟨globalImpliesLocal, strictlyWeaker, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- O omitted
  · refine ⟨unitProfile True True, fun _ => False, fun _ _ => True, fun ⟨_, h⟩ => h,
      fun _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim,
      fun _ _ _ h => h.elim, ?_⟩
    intro ⟨_, _, _, h, _⟩
    exact h
  -- B omitted
  · refine ⟨unitProfile True True, fun _ => True, fun _ _ => False, ⟨(), trivial⟩,
      fun h => (h () trivial).elim fun _ h => h, fun _ _ _ h => h.elim,
      fun _ _ _ h => h.elim, fun _ _ _ h => h.elim, fun _ _ _ _ h => h.elim, ?_⟩
    intro ⟨_, _, _, _, h, _⟩
    exact h
  -- C omitted: an existing, non-concrete bearer
  · refine ⟨unitProfile True False, fun _ => True, fun _ _ => True, ⟨(), trivial⟩,
      fun _ _ => ⟨(), trivial⟩, fun h => h () () trivial trivial,
      fun _ _ _ _ => trivial, fun _ _ _ _ => Acc.intro _ fun _ h => h.2.2.elim,
      fun _ _ _ _ _ _ hc => hc.elim, ?_⟩
    intro ⟨_, _, _, _, _, _, hc, _⟩
    exact hc
  -- E omitted: a concrete bearer existing nowhere
  · refine ⟨unitProfile False True, fun _ => True, fun _ _ => True, ⟨(), trivial⟩,
      fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial,
      fun h => h () () trivial trivial, fun _ _ _ _ => Acc.intro _ fun _ h => h.2.2.elim,
      fun _ _ _ _ _ _ _ hex => hex.elim, ?_⟩
    intro ⟨_, _, _, _, _, _, _, hex, _⟩
    exact hex
  -- local well-foundedness omitted: a two-cycle through the thinker
  · refine ⟨⟨(), trivial⟩, fun _ _ => ⟨true, rfl⟩, fun _ _ _ _ => trivial,
      fun _ _ _ _ => rfl, ?_, ?_, ?_⟩
    · intro h
      exact cycle_not_acc true (h true () trivial rfl)
    · intro _ _ x _ _ _ _ _ _
      cases x with
      | false => exact ⟨true, trivial, rfl, Bool.noConfusion⟩
      | true => exact ⟨false, trivial, rfl, Bool.noConfusion⟩
    · intro ⟨_, _, x, _, _, _, _, _, hn⟩
      have h : (false : Bool) = true := hn false trivial
      exact Bool.noConfusion h
  -- local anti-brute-root omitted: a contingent, ungrounded thinker
  · refine ⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial,
      fun _ _ _ _ => rfl, fun _ _ _ _ => Acc.intro _ fun _ h => h.2.2.elim, ?_, ?_⟩
    · intro h
      obtain ⟨_, _, _, hy⟩ := h () () () trivial trivial Relation.ReflTransGen.refl trivial rfl
        ⟨rfl, false, trivial, fun h => Bool.noConfusion h⟩
      exact hy
    · intro ⟨_, _, _, _, _, _, _, _, hn⟩
      have h : (false : Bool) = true := hn false trivial
      exact Bool.noConfusion h

end TruthCore.Results.Causality.CogitoNecessaryConcrete
