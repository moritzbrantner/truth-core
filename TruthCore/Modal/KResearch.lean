import TruthCore.Modal.ResearchFinite

/-! K experiments (#262): stipulated mathematical frames, with no historical or
metaphysical attribution. Reuses the shared semantics and finite evaluator. -/
namespace TruthCore.Modal.KResearch
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

/-- Every admissible possibility is actual at this root. Not MC by definition. -/
def PossibilityActuality {W : Type} (F : Frame W) (D : Domain W) (w : W) : Prop :=
  ∀ P, D P → Dia F P w → P w

/-- No accessibility assumptions, including seriality or reflexivity. -/
def Laws : Prop :=
  (∀ (W : Type) (F : Frame W) w,
    MC F allPredicates w ↔ ∀ v, F.access w v → v = w) ∧
  (∀ (W : Type) (F : Frame W) w,
    MC F allPredicates w ↔ PossibilityActuality F allPredicates w) ∧
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    (∀ v, ¬ F.access w v) →
      MC F D w ∧ Box F (MC F D) w ∧ ¬ Dia F (MC F D) w) ∧
  (∀ (W : Type) (F : Frame W) w (P : MProp W),
    MC F allPredicates w → ¬ Contingent F P w)

inductive World where
  | root | sink | branch | remote
  deriving DecidableEq, Repr

/-- Both root successors are sinks when link=false. When link=true, branch sees
sink. Remote is a separate reflexive component, inaccessible from the root. -/
def fork (link : Bool) : Model World Unit where
  worlds := [.root, .sink, .branch, .remote]
  complete := by
    intro w
    cases w with
    | root => exact .head _
    | sink => exact .tail _ (.head _)
    | branch => exact .tail _ (.tail _ (.head _))
    | remote => exact .tail _ (.tail _ (.tail _ (.head _)))
  edge := fun w => match w with
    | .root => fun v => match v with
      | .root => false
      | .sink => true
      | .branch => true
      | .remote => false
    | .sink => fun _ => false
    | .branch => fun v => match v with
      | .root => false
      | .sink => link
      | .branch => false
      | .remote => false
    | .remote => fun v => match v with
      | .root => false
      | .sink => false
      | .branch => false
      | .remote => true
  atom := fun w _ => match w with
    | .root => false
    | .sink => true
    | .branch => false
    | .remote => true

def p (w : World) : Prop := (fork true).atom w () = true

def language (link : Bool) : Domain World :=
  expressible (fork link).frame (fork link).valuation

/-- Exact witnesses refute the candidate implications in K, in both domains.
All contingency is model-relative; no real-world contingency is assumed. -/
def Countermodels : Prop :=
  (∀ link : Bool,
    MC (fork link).frame allPredicates .sink ∧
    MC (fork link).frame (language link) .sink ∧
    Dia (fork link).frame (MC (fork link).frame allPredicates) .root ∧
    Dia (fork link).frame (MC (fork link).frame (language link)) .root ∧
    ¬ MC (fork link).frame allPredicates .root ∧
    ¬ MC (fork link).frame (language link) .root ∧
    Contingent (fork link).frame p .root ∧
    ¬ PossibilityActuality (fork link).frame allPredicates .root ∧
    ¬ PossibilityActuality (fork link).frame (language link) .root ∧
    MC (fork link).frame allPredicates .remote ∧
    ¬ (fork link).frame.access .root .remote ∧
    World.root ≠ World.remote) ∧
  Box (fork false).frame (MC (fork false).frame allPredicates) .root ∧
  Box (fork false).frame (MC (fork false).frame (language false)) .root ∧
  (¬ Box (fork true).frame (MC (fork true).frame allPredicates) .root) ∧
  (¬ Box (fork true).frame (MC (fork true).frame (language true)) .root) ∧
  (∀ (D : Domain Unit), MC deadEnd.frame D ()) ∧
  eval (fork true) .root (.diamond (.atom ())) = true ∧
  eval (fork true) .root (.diamond (.neg (.atom ()))) = true ∧
  eval (fork true) .root (.imp (.diamond (.atom ())) (.atom ())) = false ∧
  witnesses (fork true) .root (.atom ()) = [.sink] ∧
  witnesses (fork true) .root (.neg (.atom ())) = [.branch] ∧
  counterexamples (fork true) .root (.atom ()) = [.branch]

/-- Full comprehension, restricted language and optional world extensionality
are separate configurations. The last route names every extra assumption. -/
def ScopeBoundary : Prop :=
  MC duplicates.frame (expressible duplicates.frame duplicates.valuation) false ∧
  (¬ MC duplicates.frame allPredicates false) ∧
  Dia duplicates.frame (MC duplicates.frame (expressible duplicates.frame duplicates.valuation)) false ∧
  Box duplicates.frame (MC duplicates.frame (expressible duplicates.frame duplicates.valuation)) false ∧
  PossibilityActuality duplicates.frame (expressible duplicates.frame duplicates.valuation) false ∧
  (¬ PossibilityActuality duplicates.frame allPredicates false) ∧
  (¬ PropositionalExtensionality (expressible duplicates.frame duplicates.valuation)) ∧
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    TruthCore.Logic.ExcludedMiddle →
    (∀ P, D P → D (fun v => ¬ P v)) → PropositionalExtensionality D →
    MC F D w → MC F allPredicates w)

/-- The fixed languages distinguish all four labels. Thus the K countermodels
remain countermodels when world extensionality is explicitly imposed. -/
def ExtensionalCountermodels : Prop :=
  (∀ link : Bool, PropositionalExtensionality (language link)) ∧
  (∀ (W : Type), PropositionalExtensionality (allPredicates : Domain W))

/-- Deterministic evaluator rows, including an inaccessible component. -/
def report (link : Bool) : String :=
  reprStr ((fork link).worlds.map (fun w =>
    (w, (fork link).worlds.map (fun v => (v, (fork link).edge w v)),
      eval (fork link) w (.atom ()), eval (fork link) w (.box (.atom ())),
      eval (fork link) w (.diamond (.atom ())),
      witnesses (fork link) w (.atom ()), counterexamples (fork link) w (.atom ()))))
end TruthCore.Modal.KResearch
