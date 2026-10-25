import TruthCore.Modal.KResearch

/-! Issue #264: stipulated T experiments. Reflexivity is the only assumed frame
condition. Existing shared branching/duplicate models retain their exact meanings. -/
namespace TruthCore.Modal.TResearch
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.KResearch (PossibilityActuality)
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

def branchingLanguage : Domain Bool := expressible branching.frame branching.valuation

def branchingP (w : Bool) : Prop := branching.atom w () = true

/-- T adds self-access, not transitivity, symmetry, or global world identity. -/
def Laws : Prop :=
  (∀ (W : Type) (F : Frame W), Reflexive F → ∀ w,
    (MC F allPredicates w ↔ ∀ v, F.access w v ↔ v = w) ∧
    (MC F allPredicates w ↔ Box F (MC F allPredicates) w) ∧
    (MC F allPredicates w → Dia F (MC F allPredicates) w)) ∧
  (∀ (W : Type) (F : Frame W) (D : Domain W), Reflexive F → ∀ w,
    (Box F (MC F D) w → MC F D w) ∧
    (MC F D w → Dia F (MC F D) w))

/-- The independent atom distinguishes the root (false label) and endpoint
(true label). Both full and language domains have possible, but not actual or
necessary, collapse at the root. This remains true with world extensionality. -/
def Branching : Prop :=
  Reflexive branching.frame ∧
  MC branching.frame allPredicates true ∧
  MC branching.frame branchingLanguage true ∧
  Dia branching.frame (MC branching.frame allPredicates) false ∧
  Dia branching.frame (MC branching.frame branchingLanguage) false ∧
  (¬ MC branching.frame allPredicates false) ∧
  (¬ MC branching.frame branchingLanguage false) ∧
  (¬ Box branching.frame (MC branching.frame allPredicates) false) ∧
  (¬ Box branching.frame (MC branching.frame branchingLanguage) false) ∧
  Contingent branching.frame branchingP false ∧
  (¬ PossibilityActuality branching.frame allPredicates false) ∧
  (¬ PossibilityActuality branching.frame branchingLanguage false) ∧
  PropositionalExtensionality branchingLanguage ∧
  eval branching false (.diamond (.atom ())) = true ∧
  eval branching false (.diamond (.neg (.atom ()))) = true ∧
  eval branching false (.imp (.diamond (.neg (.atom ()))) (.neg (.atom ()))) = false ∧
  witnesses branching false (.atom ()) = [false] ∧
  witnesses branching false (.neg (.atom ())) = [true]

inductive ChainWorld where
  | root | middle | endpoint
  deriving DecidableEq, Repr

/-- A reflexive chain with root→middle→endpoint but no root→endpoint edge.
The valuation is independently fixed: the atom holds exactly at endpoint. -/
def chain : Model ChainWorld Unit where
  worlds := [.root, .middle, .endpoint]
  complete := by
    intro w
    cases w with
    | root => exact .head _
    | middle => exact .tail _ (.head _)
    | endpoint => exact .tail _ (.tail _ (.head _))
  edge := fun w => match w with
    | .root => fun v => match v with
      | .root => true
      | .middle => true
      | .endpoint => false
    | .middle => fun v => match v with
      | .root => false
      | .middle => true
      | .endpoint => true
    | .endpoint => fun v => match v with
      | .root => false
      | .middle => false
      | .endpoint => true
  atom := fun w _ => match w with
    | .root => false
    | .middle => false
    | .endpoint => true

def chainLanguage : Domain ChainWorld := expressible chain.frame chain.valuation

/-- This T witness forbids silently replacing one-step reachability with its
transitive closure. It distinguishes possible MC from possible possible MC. -/
def FrameBoundary : Prop :=
  Reflexive chain.frame ∧ (¬ Transitive chain.frame) ∧ (¬ Symmetric chain.frame) ∧
  MC chain.frame allPredicates .endpoint ∧ MC chain.frame chainLanguage .endpoint ∧
  (¬ MC chain.frame allPredicates .root) ∧ (¬ MC chain.frame chainLanguage .root) ∧
  (¬ MC chain.frame allPredicates .middle) ∧ (¬ MC chain.frame chainLanguage .middle) ∧
  (¬ Dia chain.frame (MC chain.frame allPredicates) .root) ∧
  (¬ Dia chain.frame (MC chain.frame chainLanguage) .root) ∧
  Dia chain.frame (fun w => Dia chain.frame (MC chain.frame allPredicates) w) .root ∧
  (¬ Box chain.frame (MC chain.frame allPredicates) .root) ∧
  (¬ Box chain.frame (MC chain.frame chainLanguage) .root) ∧
  eval chain .root (.diamond (.atom ())) = false ∧
  eval chain .root (.diamond (.diamond (.atom ()))) = true

/-- The existing two duplicate labels form a reflexive frame. Language collapse
at every label coexists with failure of full collapse and world extensionality.
This is the configuration with no extensionality assumption; Branching supplies
a separate countermodel in which that assumption holds. -/
def ScopeBoundary : Prop :=
  Reflexive duplicates.frame ∧
  (∀ w : Bool, MC duplicates.frame (expressible duplicates.frame duplicates.valuation) w) ∧
  (∀ w : Bool, ¬ MC duplicates.frame allPredicates w) ∧
  Dia duplicates.frame (MC duplicates.frame (expressible duplicates.frame duplicates.valuation)) false ∧
  Box duplicates.frame (MC duplicates.frame (expressible duplicates.frame duplicates.valuation)) false ∧
  (¬ Dia duplicates.frame (MC duplicates.frame allPredicates) false) ∧
  (¬ Box duplicates.frame (MC duplicates.frame allPredicates) false) ∧
  PossibilityActuality duplicates.frame (expressible duplicates.frame duplicates.valuation) false ∧
  (¬ PossibilityActuality duplicates.frame allPredicates false) ∧
  (¬ PropositionalExtensionality (expressible duplicates.frame duplicates.valuation)) ∧
  (false : Bool) ≠ true

/-- Root-relative deterministic rows, using the shared evaluator without a new solver. -/
def report : String :=
  reprStr (branching.worlds.map (fun w =>
    (w, branching.worlds.map (fun v => (v, branching.edge w v)),
      eval branching w (.atom ()), eval branching w (.box (.atom ())),
      eval branching w (.diamond (.atom ())), witnesses branching w (.atom ()),
      witnesses branching w (.neg (.atom ())))),
    chain.worlds.map (fun w =>
      (w, chain.worlds.map (fun v => (v, chain.edge w v)),
        eval chain w (.diamond (.atom ())),
        eval chain w (.diamond (.diamond (.atom ()))))))
end TruthCore.Modal.TResearch
