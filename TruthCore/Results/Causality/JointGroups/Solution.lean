import TruthCore.Causality.JointGroups
import TruthCore.Results.Causality.SourceWitness.Solution
import TruthCore.Results.Causality.PluralRootConfluence.Solution
namespace TruthCore.Results.Causality.JointGroups
open TruthCore.Logic.Regress
open TruthCore.Causality
open TruthCore.Causality.JointGroups
open TruthCore.Causality.SourceForest
open TruthCore.Causality.WorldSourceRegress

theorem recorded_graph {E : Type} (K : Graph E) : (recorded K).graph = K := by
  change Graph.mk _ = Graph.mk K.edge
  congr 1
  funext y x
  apply propext
  constructor
  · rintro ⟨g, _, hg, hy⟩
    rcases hy with hy | hy
    · exact hg ▸ hy
    · exact hy.elim
  · intro hy
    exact ⟨⟨x, ⟨y, hy⟩⟩, trivial, rfl, Or.inl hy⟩

theorem source_minimal {E : Type} (K : Graph E) (s : E) (hs : K.Source s) :
    ∀ y, ¬ ancestry K y s := by
  intro y hy
  cases hy with
  | single he => exact hs ⟨_, he⟩
  | tail _ he => exact hs ⟨_, he⟩

theorem path_reverse {E : Type} (K : Graph E) (x s : E) :
    FiniteCausalPath K.edge x s ↔ Relation.ReflTransGen K.edge s x := by
  constructor
  · intro hp
    induction hp with
    | same _ => exact .refl
    | link he _ ih => exact ih.tail he
  · intro hp
    induction hp with
    | refl => exact .same _
    | tail _ he ih => exact .link he ih

theorem least_iff {E : Type} (K : Graph E) (hcy : K.NoCycles) (s : E) :
    least K s ↔ K.Source s ∧ ∀ x, FiniteCausalPath K.edge x s := by
  constructor
  · intro hl
    refine ⟨?_, fun x => (path_reverse K x s).mpr (hl x)⟩
    rintro ⟨y, he⟩
    exact hcy y (.head' he (hl y))
  · rintro ⟨_, hp⟩ x
    exact (path_reverse K x s).mp (hp x)

theorem order_schema : OrderSchema := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E G h hcy
    exact { irrefl := hcy, trans := fun _ _ _ hab hbc => hab.trans hbc }
  · intro B E G S m hw x
    obtain ⟨s, hp, hs⟩ := hw |> m.actualGraph.controls_of_wellFounded |>.2.2 x
    exact ⟨s, hp, source_minimal _ s hs⟩
  · intro B E G S m hw hn
    obtain ⟨x⟩ := hn
    obtain ⟨s, _, hs⟩ := (m.actualGraph.controls_of_wellFounded hw).2.2 x
    exact ⟨s, hs⟩
  · intro E K hcy s
    exact least_iff K hcy s

theorem event_forall (p : Event → Prop) :
    (∀ e, p e) ↔ p .a ∧ p .b ∧ p .c ∧ p .enabled ∧ p .outcome := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _, h _⟩
  · rintro ⟨ha, hb, hc, he, ho⟩ e; cases e <;> assumption
theorem illustrations : IllustrationControls := by
  simp only [IllustrationControls]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext e; cases e <;> simp [Groups.members, ignition]
  · ext e; cases e <;> simp [Groups.members, ignition]
  · simp [ignition]
  · simp [ignition]

theorem cooperation : CooperationControls := by
  simp [CooperationControls, Exercise.coherent, Exercise.jointlySufficient,
    Exercise.indispensable, Exercise.redundant, Exercise.suffices,
    fixture, fixtureGroups, Groups.members, event_forall,
    Prod.forall, Bool.forall_bool, Set.mem_ofPred_eq]

theorem overlap : RecordedOverlap := by
  refine ⟨recorded_graph _, ?_, ?_, SourceWitness.overlap_control⟩
  · intro g h he
    exact Subtype.ext he
  · intro n
    ext y
    change GroundingAllowsRegress.link y.val (some n) ↔
      y.val = none ∨ y.val = some (n + 1)
    cases y with
    | mk y hy => cases y <;> simp [GroundingAllowsRegress.link]

theorem plural : PluralMinima := by
  have old := PluralRootConfluence.control
  have ⟨_, _, _, hw, hl, hr, hne, _, _, _, _, _⟩ := old
  refine ⟨old, source_minimal _ _ hl, source_minimal _ _ hr, ?_⟩
  rintro ⟨s, hs⟩
  have paths := (least_iff _ (PluralRootConfluence.graph.controls_of_wellFounded hw).1 s).mp hs
  have eqOfSource : ∀ x, PluralRootConfluence.graph.Source x →
      FiniteCausalPath PluralRootConfluence.graph.edge x s → x = s := by
    intro x hx hp
    cases hp with
    | same => rfl
    | link he _ => exact (hx ⟨_, he⟩).elim
  exact hne ((eqOfSource _ hl (paths.2 _)).trans (eqOfSource _ hr (paths.2 _)).symm)

theorem omissions : JointGroups.OmissionControls := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, cooperation.2.1, id⟩
    exact ⟨trivial, fun _ h => h.elim⟩
  · refine ⟨⟨Event.a⟩, ?_⟩
    rintro ⟨x⟩
    exact x.property
  · refine ⟨trivial, ?_, ?_⟩
    · simp [Graph.Source, Groups.graph, Groups.members, emptyRecord]
    · rintro ⟨x⟩; exact x.property
  · change ¬ IsStrictOrder Unit (ancestry (⟨fun _ _ => True⟩ : Graph Unit))
    intro h
    exact h.irrefl () (Relation.TransGen.single trivial)

/-- Frozen #733 conditional structure and concrete omission/countermodels;
no actual-world sufficiency, acyclicity, WF or explanatory adequacy asserted. -/
theorem certificate : TruthCore.Causality.JointGroups.Certificate :=
  ⟨order_schema, illustrations, cooperation, overlap, plural, omissions⟩
end TruthCore.Results.Causality.JointGroups
