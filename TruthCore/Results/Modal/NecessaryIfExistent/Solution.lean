import TruthCore.Modal.NecessaryIfExistent
namespace TruthCore.Results.Modal.NecessaryIfExistent
open TruthCore.Modal TruthCore.Modal.NecessaryIfExistent
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

/-- Euclidean accessibility alone transports the boxed conditional across
siblings. Neither reflexivity, transitivity nor seriality is used. -/
theorem forward {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) :
    Dia F G w → Box F G w := by
  rintro ⟨v, hv, hg⟩ z hz
  exact hn v hv hg z (he w v z hv hz)

/-- Reverse escalation is constructive under exactly the same modal premise. -/
theorem reverse {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) :
    Dia F (fun v => ¬ G v) w → Box F (fun v => ¬ G v) w := by
  rintro ⟨v, hv, hng⟩ z hz hg
  exact hng (hn z hz hg v (he w z v hz hv))

/-- EM supplies coverage; it chooses no preferred disjunct. -/
theorem certificate : Certificate := by
  intro W F G w he hn hem
  refine ⟨forward F G w he hn, reverse F G w he hn, ?_⟩
  rcases hem (Dia F G w) with hp | hnp
  · exact Or.inl (forward F G w he hn hp)
  · exact Or.inr (fun v hv hg => hnp ⟨v, hv, hg⟩)

/-- A successor, unlike coverage, rules out the conjunction. Empty successor
sets must not be called an exclusive dichotomy. -/
theorem exclusive {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (hs : ∃ v, F.access w v) :
    ¬ (Box F G w ∧ Box F (fun v => ¬ G v) w) := by
  rintro ⟨hp, hn⟩
  obtain ⟨v, hv⟩ := hs
  exact hn v hv (hp v hv)

/-- S5 specialization reuses the K5 proof and the existing cube semantics. -/
theorem s5 {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (hs : FrameSatisfies .S5 F) (hn : NecessaryIf F G w)
    (hem : TruthCore.Logic.ExcludedMiddle) : Matrix F G w ∧
      ¬ (Box F G w ∧ Box F (fun v => ¬ G v) w) := by
  exact ⟨certificate W F G w hs.2 hn hem,
    exclusive F G w ⟨w, hs.1 w⟩⟩

/-- The proponent still owes PossibleExistence; the conditional alone supplies none. -/
theorem positive {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) (hp : PossibleExistence F G w) :
    NecessaryExistence F G w := forward F G w he hn hp

/-- The reverse rival owes PossibleNonexistence under the same modal assumptions. -/
theorem negative {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w) (hp : PossibleNonexistence F G w) :
    ImpossibleExistence F G w := reverse F G w he hn hp

/-- Coverage chooses no side; explicit classicality is needed only here. -/
theorem coverage {W : Type} (F : Frame W) (G : W → Prop) (w : W)
    (he : Euclidean F) (hn : NecessaryIf F G w)
    (hem : TruthCore.Logic.ExcludedMiddle) : Coverage F G w :=
  (certificate W F G w he hn hem).2.2

set_option synthInstance.maxSize 4096 in
theorem controls : Controls := by
  dsimp [Controls, FrameSatisfies, ActualConditional, NecessaryIf, Box, Dia,
    Euclidean, Serial, Reflexive, Transitive, ascending, universal, empty, identity, G]
  decide
end TruthCore.Results.Modal.NecessaryIfExistent
