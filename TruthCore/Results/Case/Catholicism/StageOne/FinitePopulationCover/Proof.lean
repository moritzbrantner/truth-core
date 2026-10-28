import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.FinitePopulationCover

/-! Conditional finite-population bridge (#533). Stipulated semantics only.
The ambient rigid roster can be infinite. Cover and amalgamation remain open
metaphysical commitments; these consequences do not establish either policy. -/
namespace TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Modal
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)
universe u v
variable {W : Type u} {I : Type v}

/-- Constructive finite omission induction. The empty list requires a successor;
the step combines its omission world with the next individual's absence world. -/
theorem finite_omission (F : Frame W) (present : ExistsAt W I) (w : W)
    (hs : AccessibleSuccessor F w) (ha : AbsenceAmalgamation F present w)
    (hc : IndividualContingency F present w) (xs : List I) :
    ∃ v, F.access w v ∧ ∀ x, x ∈ xs → ¬ present x v := by
  induction xs with
  | nil =>
    obtain ⟨v, hv⟩ := hs
    exact ⟨v, hv, fun x hx => False.elim (List.not_mem_nil hx)⟩
  | cons x xs ih =>
    obtain ⟨u, hu, hxs⟩ := ih
    obtain ⟨v, hv, hx⟩ := hc x
    obtain ⟨z, hz, hsub⟩ := ha u v hu hv
    refine ⟨z, hz, ?_⟩
    intro y hy hyp
    cases hy with
    | head => exact hx (hsub x hyp).2
    | tail _ hmem => exact hxs y hmem (hsub y hyp).1

/-- A full cover turns omission of its finite list into omission of everyone. -/
theorem finite_cover_joint_absence (F : Frame W) (present : ExistsAt W I) (w : W)
    (hs : AccessibleSuccessor F w) (ha : AbsenceAmalgamation F present w)
    (hc : IndividualContingency F present w) (hf : FinitePopulationCover F present w) :
    JointAbsence F present w := by
  obtain ⟨xs, hcover⟩ := hf
  obtain ⟨v, hv, hn⟩ := finite_omission F present w hs ha hc xs
  exact ⟨v, hv, fun ⟨x, hx⟩ => hn x (hcover v hv x hx) hx⟩

/-- Constructively necessary population refutes universal individual contingency. -/
theorem finite_cover_not_contingency (F : Frame W) (present : ExistsAt W I) (w : W)
    (hs : AccessibleSuccessor F w) (ha : AbsenceAmalgamation F present w)
    (hf : FinitePopulationCover F present w) (hd : DeDicto F present w) :
    ¬ IndividualContingency F present w := by
  intro hc
  obtain ⟨v, hv, hn⟩ := finite_cover_joint_absence F present w hs ha hc hf
  exact hn (hd v hv)

/-- The positive witness requires the explicit excluded-middle proposition.
No choice or implicit classical tactic is used. -/
theorem finite_cover_deRe (F : Frame W) (present : ExistsAt W I) (w : W)
    (em : TruthCore.Logic.ExcludedMiddle)
    (hs : AccessibleSuccessor F w) (ha : AbsenceAmalgamation F present w)
    (hf : FinitePopulationCover F present w) (hd : DeDicto F present w) :
    DeRe F present w := by
  rcases em (DeRe F present w) with h | hn
  · exact h
  · apply False.elim
    apply finite_cover_not_contingency F present w hs ha hf hd
    intro x
    rcases em (∃ v, F.access w v ∧ ¬ present x v) with hx | hx
    · exact hx
    · apply False.elim
      apply hn
      refine ⟨x, fun v hv => ?_⟩
      rcases em (present x v) with hp | hp
      · exact hp
      · exact False.elim (hx ⟨v, hv, hp⟩)

/-- A finite complete roster is sufficient but not required by the bridge. -/
theorem roster_cover (F : Frame W) (present : ExistsAt W I) (w : W)
    (xs : List I) (h : ∀ x, x ∈ xs) : FinitePopulationCover F present w :=
  ⟨xs, fun _ _ x _ => h x⟩

/-- The alternating population cannot amalgamate its two singleton worlds. -/
theorem alternating_not_amalgamation :
    ¬ AbsenceAmalgamation alternatingFrame alternatingExists false := by
  intro ha
  obtain ⟨z, _, hz⟩ := ha false true trivial trivial
  have h := hz z rfl
  exact Bool.false_ne_true (h.1.symm.trans h.2)

/-- Without successors the cover and amalgamation are vacuous, but joint absence
is impossible, even for an empty individual roster. This explains `hs`. -/
theorem successor_free_control :
    let F : Frame Unit := ⟨fun _ _ => False⟩
    let p : ExistsAt Unit Empty := fun _ _ => False
    FinitePopulationCover F p () ∧ AbsenceAmalgamation F p () ∧
    IndividualContingency F p () ∧ ¬ JointAbsence F p () := by
  refine ⟨⟨[], fun _ hv => False.elim hv⟩, ?_, ?_, ?_⟩
  · intro _ _ hv
    exact False.elim hv
  · intro x
    exact Empty.elim x
  · intro ⟨_, hv, _⟩
    exact hv
/-- Tails are populated and amalgamate via max, but each fixed member is absent
later. Hence there is no necessary individual and no finite population cover. -/
theorem tail_control :
    DeDicto finiteCoverTailFrame finiteCoverTailPresent 0 ∧
    IndividualContingency finiteCoverTailFrame finiteCoverTailPresent 0 ∧
    AbsenceAmalgamation finiteCoverTailFrame finiteCoverTailPresent 0 ∧
    ¬ DeRe finiteCoverTailFrame finiteCoverTailPresent 0 ∧
    ¬ FinitePopulationCover finiteCoverTailFrame finiteCoverTailPresent 0 := by
  have hd : DeDicto finiteCoverTailFrame finiteCoverTailPresent 0 :=
    fun n _ => ⟨n, Nat.le_refl n⟩
  have hc : IndividualContingency finiteCoverTailFrame finiteCoverTailPresent 0 :=
    fun x => ⟨x + 1, trivial, Nat.not_succ_le_self x⟩
  have hmax : ∀ u v : Nat, u ≤ max u v ∧ v ≤ max u v := by
    intro u v
    rw [Nat.max_def]
    split
    · rename_i h
      exact ⟨h, Nat.le_refl _⟩
    · rename_i h
      exact ⟨Nat.le_refl _, Nat.le_of_lt (Nat.lt_of_not_ge h)⟩
  have ha : AbsenceAmalgamation finiteCoverTailFrame finiteCoverTailPresent 0 := by
    intro u v _ _
    exact ⟨max u v, trivial, fun x hx =>
      ⟨Nat.le_trans ((hmax u v).1) hx, Nat.le_trans ((hmax u v).2) hx⟩⟩
  refine ⟨hd, hc, ha, ?_, ?_⟩
  · intro ⟨x, hx⟩
    exact Nat.not_succ_le_self x (hx (x + 1) trivial)
  · intro hf
    exact finite_cover_not_contingency _ _ 0 ⟨0, trivial⟩ ha hf hd hc

end TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
