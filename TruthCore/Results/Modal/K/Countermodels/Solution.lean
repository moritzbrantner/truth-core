import TruthCore.Results.Modal.K.Laws.Solution
namespace TruthCore.Results.Modal.K.Countermodels
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.KResearch
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

theorem sink_collapse (link : Bool) (D : Domain World) :
    MC (fork link).frame D .sink := by
  intro P _ _ v hv
  cases v <;> cases hv

theorem remote_collapse (link : Bool) : MC (fork link).frame allPredicates .remote := by
  apply (Laws.full_iff_successors _ _).mpr
  intro v hv
  cases v <;> first | rfl | cases hv

theorem root_not_language (link : Bool) : ¬ MC (fork link).frame (language link) .root := by
  intro h
  have hd : language link (fun w => Holds (fork link).frame (fork link).valuation w
      (.neg (.atom ()))) := ⟨.neg (.atom ()), rfl⟩
  have hr : Holds (fork link).frame (fork link).valuation .root (.neg (.atom ())) := by
    intro hf; cases hf
  have hs := h _ hd hr .sink rfl
  exact hs rfl

theorem root_not_full (link : Bool) : ¬ MC (fork link).frame allPredicates .root := by
  intro h
  exact root_not_language link (restrict _ allPredicates (language link) .root
    (fun _ _ => trivial) h)

theorem root_contingent (link : Bool) : Contingent (fork link).frame p .root := by
  refine ⟨⟨.sink, rfl, rfl⟩, ⟨.branch, rfl, ?_⟩⟩
  intro h; cases h

theorem not_actuality (link : Bool) (D : Domain World) (hp : D p) :
    ¬ PossibilityActuality (fork link).frame D .root := by
  intro h
  have hf := h p hp ⟨.sink, rfl, rfl⟩
  cases hf

theorem p_expressible (link : Bool) : language link p := ⟨.atom (), rfl⟩

theorem branch_not_language : ¬ MC (fork true).frame (language true) .branch := by
  intro h
  have hd : language true (fun w => Holds (fork true).frame (fork true).valuation w
      (.neg (.atom ()))) := ⟨.neg (.atom ()), rfl⟩
  have hb : Holds (fork true).frame (fork true).valuation .branch (.neg (.atom ())) := by
    intro hf; cases hf
  exact h _ hd hb .sink rfl rfl

theorem fork_box (D : Domain World) : Box (fork false).frame (MC (fork false).frame D) .root := by
  intro v hv
  cases v with
  | root => cases hv
  | sink => exact sink_collapse false D
  | branch =>
    intro P _ _ v hv
    cases v <;> cases hv
  | remote => cases hv

theorem checks : Countermodels := by
  refine ⟨?_, fork_box allPredicates, fork_box (language false), ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro link
    refine ⟨sink_collapse link allPredicates, sink_collapse link (language link),
      ⟨.sink, rfl, sink_collapse link allPredicates⟩,
      ⟨.sink, rfl, sink_collapse link (language link)⟩,
      root_not_full link, root_not_language link, root_contingent link,
      not_actuality link allPredicates trivial, not_actuality link (language link) (p_expressible link),
      remote_collapse link, ?_, ?_⟩
    · intro h; cases h
    · intro h; cases h
  · intro h
    exact branch_not_language (restrict _ allPredicates (language true) .branch
      (fun _ _ => trivial) (h .branch rfl))
  · intro h; exact branch_not_language (h .branch rfl)
  · intro D P _ _ v hv; cases hv
end TruthCore.Results.Modal.K.Countermodels
