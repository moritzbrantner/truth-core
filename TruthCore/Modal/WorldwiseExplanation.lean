import TruthCore.Models.PSR

/-!
Issue #465: an explanation at every world need not be the *same* explanation
at every world. Reuse the world-relative existence, tagged existence facts,
reason tokens, and existence-PSR from the established PSR-scope investigation.

The examples concern stipulated explanatory assignments. `Sound` guarantees
only that the explanandum exists at the relevant world; it does not validate
an explanation as genuinely sufficient in metaphysical reality.
-/
namespace TruthCore.Modal.WorldwiseExplanation

open TruthCore.Explanation.ExistencePSR
open TruthCore.German.Kant.CosmologicalInference

variable {World Being : Type}

/-- One rigid reason token explains the existence of this same being wherever
it exists. Unlike `ExistencePSR`, this puts `∃ reason` outside `∀ world`. -/
def StableExplanation (m : Model World Being) (x : Being) : Prop :=
  ∃ r, ∀ w, m.ontic.ExistsAt w x → m.explains w r (.fact x)

/-- A substantive bridge: any reason explaining the selected existent at one
world also explains it at another world where the same individual exists. -/
def ReasonInvariant (m : Model World Being) (x : Being) : Prop :=
  ∀ w v r, m.explains w r (.fact x) → m.ontic.ExistsAt v x →
    m.explains v r (.fact x)

/-- A stable reason gives an explanation at each world of existence. -/
theorem stable_implies_worldwise (m : Model World Being) (x : Being)
    (h : StableExplanation m x) :
    ∀ w, m.ontic.ExistsAt w x → ∃ r, m.explains w r (.fact x) := by
  obtain ⟨r, hr⟩ := h
  intro w hw
  exact ⟨r, hr w hw⟩

/-- Worldwise reasons become a stable reason only after adding a cross-world
invariance bridge and requiring an actually existing witness somewhere. -/
theorem worldwise_and_invariance_implies_stable
    (m : Model World Being) (x : Being)
    (hExists : ∃ w, m.ontic.ExistsAt w x)
    (hWorldwise : ∀ w, m.ontic.ExistsAt w x → ∃ r, m.explains w r (.fact x))
    (hInvariant : ReasonInvariant m x) : StableExplanation m x := by
  obtain ⟨w, hw⟩ := hExists
  obtain ⟨r, hr⟩ := hWorldwise w hw
  exact ⟨r, fun v hv => hInvariant w v r hr hv⟩

/-- Two worlds in which the same being exists but no explanatory token is
admitted at both exclude a stable explanation. This is a general incompatibility
rule, not an assumption that genuine explanations must have that pattern. -/
theorem disjoint_reasons_preclude_stable
    (m : Model World Being) (x : Being) (w v : World)
    (hw : m.ontic.ExistsAt w x) (hv : m.ontic.ExistsAt v x)
    (hDisjoint : ∀ r, m.explains w r (.fact x) →
      ¬ m.explains v r (.fact x)) : ¬ StableExplanation m x := by
  rintro ⟨r, hr⟩
  exact hDisjoint r (hr w hw) (hr v hv)

/-- Finite alternating-reason model: the necessarily existing bearer `false`
is explained by `.circumstance false` at world `false`, but by
`.circumstance true` at world `true`. There is no fixed reason token for it. -/
def alternating : Model Bool Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ x => x = false
    Causes := fun _ _ _ => False
  }
  explains := fun w r f => match f with
    | .fact x => x = false ∧ r = .circumstance w

theorem alternatingSound : Sound alternating := by
  intro w x r hr
  exact hr.1

theorem alternatingPSR : ExistencePSR alternating := by
  intro w x hx
  exact ⟨.circumstance w, hx, rfl⟩

theorem alternatingNecessary : NecessaryBeing alternating.ontic false := by
  refine ⟨false, rfl, ?_⟩
  intro w _
  rfl

theorem alternatingNotStable : ¬ StableExplanation alternating false := by
  rintro ⟨r, hr⟩
  have hFalse := hr false rfl
  have hTrue := hr true rfl
  have hDifferent : (Reason.circumstance false : Reason Bool) =
      .circumstance true := hFalse.2.symm.trans hTrue.2
  cases hDifferent

/-- A non-vacuous universal-accessibility model with a necessary individual
and an explanation for every existent at every world, but no fixed reason for
that individual across worlds. This refutes a quantifier-shift inference, not
the unrestricted PSR itself. -/
def WorldwiseWithoutStable : Prop :=
  ∃ m : Model Bool Bool,
    (∀ w v, m.ontic.frame.access w v) ∧
    Sound m ∧ ExistencePSR m ∧ NecessaryBeing m.ontic false ∧
    ¬ StableExplanation m false

theorem worldwiseWithoutStable : WorldwiseWithoutStable := by
  exact ⟨alternating, (by intro _ _; trivial), alternatingSound,
    alternatingPSR, alternatingNecessary, alternatingNotStable⟩

/-- The established intrinsic-reason model also witnesses the *other*
configuration: local and stable explanation can coexist. Its explanation tag
is an analyst's stipulation, not a proof of real intrinsic sufficiency. -/
theorem intrinsicModelHasStableReason :
    StableExplanation TruthCore.Models.PSR.Intrinsic.model false := by
  refine ⟨.intrinsic false, ?_⟩
  intro w _
  exact ⟨rfl, rfl⟩

end TruthCore.Modal.WorldwiseExplanation
