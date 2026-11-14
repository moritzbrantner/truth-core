module

public import TruthCore.Modal.PossibilityTransfer
public import TruthCore.Modal.FixedInitial535

/-! #1588: links the fixed-initial-history profile of #535 to the two-relation
possibility transfer of #438. Analyst formulation, attribution deferred: the
worlds are candidate history descriptions, `E` an epistemic admission profile
and the history's own frame the stipulated metaphysical (M) profile. Nothing here
says which profile is metaphysically adequate, that conceivability yields
possibility, or that fixed-history necessity is false. Reuses `History`,
`Rigid`, `NecessaryAt`, `IncludedAt`, `Box` and `Dia` without new modal
semantics. -/

@[expose] public section

namespace TruthCore.Modal.InitialHistoryTransfer1588
open TruthCore.Modal.PossibilityTransfer
open TruthCore.Modal.FixedInitial535
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)

/-- Inclusion of E-successors in M-successors at `w`, restricted to the
witnesses of one description `P`. Pointwise, not a modal axiom. -/
def IncludedOn {D : Type} (E M : Frame D) (P : MProp D) (w : D) : Prop :=
  ∀ v, E.access w v → P v → M.access w v

/-- Alternative start (bearer): the selected actual initial bearer `b` is absent. -/
def AltBearer {W B D : Type} (h : History W B D) (b : B) : MProp W :=
  fun v => ¬ h.ontic.ExistsAt v b

/-- Alternative start (type): the selected initial description differs from `a`'s. -/
def AltType {W B D : Type} (h : History W B D) (a : W) : MProp W :=
  fun v => h.description v ≠ h.description a

/-- Restricted inclusion suffices for transferring one description. -/
def RestrictedTransfer : Prop :=
  ∀ (D : Type) (E M : Frame D) (P : MProp D) (w : D),
    IncludedOn E M P w → Dia E P w → Dia M P w

/-- For a complete (singleton) history description, transfer is exactly the
single access inclusion for that history. -/
def CompleteDescriptionTransfer : Prop :=
  ∀ (D : Type) (E M : Frame D) (w v : D),
    (Dia E (fun u => u = v) w → Dia M (fun u => u = v) w) ↔
      (E.access w v → M.access w v)

/-- Both transfer refinements together. -/
def TransferRefinement : Prop := RestrictedTransfer ∧ CompleteDescriptionTransfer

/-- Incompatible triad, stated as a conditional: under a rigid M-profile at `a`
with actual initial bearer `b`, an E-admissible history omitting `b` and
inclusion of E in M on such histories cannot all hold. Which member to give up
is NOT decided here. The inclusion member is a sufficient strengthening of the
single discriminating edge `OmissionEdge` below. -/
def RigidTriad : Prop :=
  ∀ (W B D : Type) (h : History W B D) (E : Frame W) (a : W) (b : B),
    Rigid h a → h.initial b a → Dia E (AltBearer h b) a →
      ¬ IncludedOn E h.ontic.frame (AltBearer h b) a

/-- Conversely, a rigid M-profile plus full inclusion of E in M at `a` makes
the actual initial witness present at every E-admitted history. -/
def RigidInclusionNecessity : Prop :=
  ∀ (W B D : Type) (h : History W B D) (E : Frame W) (a : W),
    Rigid h a → IncludedAt E h.ontic.frame a →
      ∃ b, h.initial b a ∧ Box E (fun v => h.ontic.ExistsAt v b) a

/-- Finite model: four candidate histories. 0 actual; 1 same initial bearer,
different later observation; 2 same initial description, different initial
bearer; 3 different initial description and bearer. -/
def root (w : Fin 4) : Fin 3 :=
  if w = 2 then 1 else if w = 3 then 2 else 0

/-- One history profile per M-frame; only initial bearers exist, no grounds. -/
def history4 (M : Frame (Fin 4)) : History (Fin 4) (Fin 3) Bool where
  ontic := { frame := M, ExistsAt := fun w b => b = root w, Causes := fun _ _ _ => False }
  initial := fun b w => b = root w
  description := fun w => decide (w = 3)
  later := fun w => decide (w = 1)
  grounds := fun _ _ _ => False

/-- Epistemic admission: every candidate history. -/
def epistemic4 : Frame (Fin 4) := ⟨fun _ _ => True⟩
/-- Strong (rigid) reading: histories sharing the selected initial bearer. -/
def rigidAccess : Frame (Fin 4) := ⟨fun a v => root v = root a⟩
/-- Weaker (qualitative) reading: histories sharing the initial description. -/
def descAccess : Frame (Fin 4) := ⟨fun a v => decide (v = 3) = decide (a = 3)⟩

/-- Same initial description, but the actual initial bearer absent. -/
def sameTypeAltBearer : MProp (Fin 4) :=
  fun v => v ≠ 3 ∧ root v ≠ 0

/-- Structural surrogate, not a cosmology. History 2 differs from history 0
only by its primitive bearer label, so every separation using it presupposes
bearer-distinct qualitative duplicates (OPEN; anti-haecceitist individuation
would identify 0 and 2). The history-3 / `AltType` separation does not use it.
Joint checked model facts. All three frames are equivalences, so the
separations are not empty-access artifacts. Under the rigid profile the actual
initial bearer 0 is M-necessary with later variation; the bearer-omitting and
type-changing descriptions are E-admissible and M-inadmissible, and M-necessity
of bearer 0 does not transfer to E. Under the qualitative profile the
bearer-omitting description is admitted and no necessity of bearer 0 follows.
Inclusion restricted to `sameTypeAltBearer` holds for the qualitative profile
while full inclusion and inclusion on all bearer omissions fail, yet transfer of
those descriptions succeeds. -/
def Model : Prop :=
  Reflexive epistemic4 ∧ Symmetric epistemic4 ∧ Transitive epistemic4 ∧
  Reflexive rigidAccess ∧ Symmetric rigidAccess ∧ Transitive rigidAccess ∧
  Reflexive descAccess ∧ Symmetric descAccess ∧ Transitive descAccess ∧
  Rigid (history4 rigidAccess) 0 ∧ LaterVariation (history4 rigidAccess) 0 ∧
  NecessaryAt (history4 rigidAccess).ontic 0 0 ∧
  IncludedAt rigidAccess epistemic4 0 ∧ ¬ IncludedAt epistemic4 rigidAccess 0 ∧
  Dia epistemic4 (AltBearer (history4 rigidAccess) 0) 0 ∧
  ¬ Dia rigidAccess (AltBearer (history4 rigidAccess) 0) 0 ∧
  Dia epistemic4 (AltType (history4 rigidAccess) 0) 0 ∧
  ¬ Dia rigidAccess (AltType (history4 rigidAccess) 0) 0 ∧
  ¬ Box epistemic4 (fun v => (history4 rigidAccess).ontic.ExistsAt v 0) 0 ∧
  SameDescription (history4 descAccess) 0 ∧ ¬ Rigid (history4 descAccess) 0 ∧
  ¬ NecessaryAt (history4 descAccess).ontic 0 0 ∧
  Dia descAccess (AltBearer (history4 descAccess) 0) 0 ∧
  ¬ Dia descAccess (AltType (history4 descAccess) 0) 0 ∧
  IncludedOn epistemic4 descAccess sameTypeAltBearer 0 ∧
  ¬ IncludedOn epistemic4 descAccess (AltBearer (history4 descAccess) 0) 0 ∧
  ¬ IncludedAt epistemic4 descAccess 0 ∧
  Dia descAccess sameTypeAltBearer 0

/-- The single discriminating edge: some E-admitted history lacking `b` is
M-accessible from `a`. Restricted inclusion on all such histories is a
sufficient strengthening of it, given one E-admitted omission. -/
def OmissionEdge {W B D : Type} (h : History W B D) (E : Frame W) (a : W) (b : B) :
    Prop :=
  ∃ v, E.access a v ∧ AltBearer h b v ∧ h.ontic.frame.access a v

/-- A rigid M-profile denies this edge for every actual initial bearer. -/
def RigidDeniesEdge : Prop :=
  ∀ (W B D : Type) (h : History W B D) (E : Frame W) (a : W) (b : B),
    Rigid h a → h.initial b a → ¬ OmissionEdge h E a b

/-- In the structural surrogate: the qualitative profile has the edge (via the
bearer-distinct qualitative duplicate, history 2) while failing restricted
inclusion on all bearer omissions (history 3); the rigid profile lacks the edge.
History 2 differs from 0 only by its primitive bearer label, so this separation
presupposes bearer-distinct qualitative duplicates. -/
def EdgeSeparation : Prop :=
  OmissionEdge (history4 descAccess) epistemic4 0 0 ∧
  ¬ IncludedOn epistemic4 descAccess (AltBearer (history4 descAccess) 0) 0 ∧
  ¬ OmissionEdge (history4 rigidAccess) epistemic4 0 0

def EdgeChecks : Prop := RigidDeniesEdge ∧ EdgeSeparation

def Checks : Prop :=
  TransferRefinement ∧ RigidTriad ∧ RigidInclusionNecessity ∧ Model
end TruthCore.Modal.InitialHistoryTransfer1588
