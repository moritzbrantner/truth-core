import TruthCore.Modal.NecessaryIfConnectivity
namespace TruthCore.Results.Modal.NecessaryIfConnectivity
open TruthCore.Modal TruthCore.Modal.NecessaryIfExistent
open TruthCore.Modal.NecessaryIfConnectivity
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

/-- The boxed conditional propagates truth along exactly the masked paths. -/
theorem propagate {W : Type} (F : Frame W) (G : W → Prop) (w a b : W)
    (hn : NecessaryIf F G w)
    (hp : Relation.ReflTransGen (maskedStep F w) a b) (hg : G a) : G b := by
  induction hp with
  | refl => exact hg
  | @tail b c _ hbc ih => exact hn b hbc.1 ih c hbc.2

/-- If the endpoint is again a successor, every traversed edge can be
restricted to the induced successor subgraph. An exit cannot return. -/
theorem restrict_path {W : Type} (F : Frame W) (w a b : W)
    (hp : Relation.ReflTransGen (maskedStep F w) a b) (hb : F.access w b) :
    Relation.ReflTransGen (fun x y => maskedStep F w x y ∧ F.access w y) a b := by
  revert hb
  induction hp with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    intro hc
    exact (ih hbc.1).tail ⟨hbc, hc⟩

/-- Necessity uses the characteristic predicate of masked reachability;
sufficiency propagates the possible witness to every sibling successor. -/
theorem correspondence {W : Type} (F : Frame W) (w : W) :
    ForwardAt F w ↔ SuccessorConnected F w := by
  constructor
  · intro h a b ha hb
    let G := fun z => Relation.ReflTransGen (maskedStep F w) a z
    have hn : NecessaryIf F G w := by
      intro v hv hg z hz
      exact hg.tail ⟨hv, hz⟩
    exact h G hn ⟨a, ha, Relation.ReflTransGen.refl⟩ b hb
  · intro hc G hn hp b hb
    obtain ⟨a, ha, hg⟩ := hp
    exact propagate F G w a b hn (hc a b ha hb) hg

/-- Euclidean one-step sibling access is stronger than the exact path condition. -/
theorem euclidean {W : Type} (F : Frame W) (w : W) (he : Euclidean F) :
    SuccessorConnected F w := by
  intro a b ha hb
  exact Relation.ReflTransGen.single ⟨ha, he w a b ha hb⟩

/-- T+B supplies a two-step sibling path through the reflexive standpoint. -/
theorem reflexive_symmetric {W : Type} (F : Frame W) (w : W)
    (hr : Reflexive F) (hs : Symmetric F) : SuccessorConnected F w := by
  intro a b ha hb
  exact (Relation.ReflTransGen.single ⟨ha, hs w a ha⟩).tail ⟨hr w, hb⟩

theorem line_reflexive : Reflexive line := fun _ => Or.inl rfl

theorem line_symmetric : Symmetric line := by
  intro a b h
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem line_not_euclidean : ¬ Euclidean line := by
  intro he
  have h := he none (some false) (some true)
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
  rcases h with h | h | h <;> cases h

/-- The same exact condition validates both rival escalations. Only the
coverage branch uses explicit EM; no actual truth is inferred from a box. -/
theorem matrix {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (hc : SuccessorConnected F w) (hn : NecessaryIf F G w)
    (hem : TruthCore.Logic.ExcludedMiddle) : Matrix F G w := by
  have hf := (correspondence F w).mpr hc G hn
  refine ⟨hf, ?_, ?_⟩
  · rintro ⟨v, hv, hng⟩ z hz hg
    exact hng (propagate F G w z v hn (hc z v hz hv) hg)
  · rcases hem (Dia F G w) with hp | hnp
    · exact Or.inl (hf hp)
    · exact Or.inr (fun v hv hg => hnp ⟨v, hv, hg⟩)

theorem certificate : TruthCore.Modal.NecessaryIfConnectivity.Certificate := by
  exact ⟨fun _ F w => correspondence F w,
    fun _ F w => euclidean F w,
    fun _ F w => reflexive_symmetric F w,
    line_reflexive, line_symmetric,
    fun w => reflexive_symmetric line w line_reflexive line_symmetric,
    line_not_euclidean⟩
end TruthCore.Results.Modal.NecessaryIfConnectivity
