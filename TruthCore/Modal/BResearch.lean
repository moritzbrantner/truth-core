import TruthCore.Modal.KResearch

/-! Issue #266: stipulated B-frame experiments, not historical/metaphysical claims. -/
namespace TruthCore.Modal.BResearch
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

/-- Local back-edge plus identity expressibility; no global frame axioms. -/
def Laws : Prop :=
  (∀ (W : Type) (F : Frame W) (D : Domain W) w v,
    F.access v w → IdentityAdmissible D v → MC F D v → w = v) ∧
  (∀ (W : Type) (F : Frame W) w,
    Symmetric F → Dia F (MC F allPredicates) w → MC F allPredicates w) ∧
  (∀ (W : Type) (F : Frame W) w,
    Reflexive F → Symmetric F →
      (MC F allPredicates w ↔ Dia F (MC F allPredicates) w) ∧
      (MC F allPredicates w ↔ Box F (MC F allPredicates) w))

/-- Necessary and actual full collapse coincide on symmetric frames, even at sinks. -/
def NecessarySymmetry : Prop :=
  ∀ (W : Type) (F : Frame W) w,
    Symmetric F → (MC F allPredicates w ↔ Box F (MC F allPredicates) w)

/-- Closure assumptions are part of the theorem, not hidden domain defaults. -/
def LanguagePropagation : Prop :=
  ∀ (W : Type) (F : Frame W) (D : Domain W) w,
    TruthCore.Logic.ExcludedMiddle →
    (∀ P, D P → D (fun x => ¬ P x)) →
    (∀ P, D P → D (Box F P)) →
    Symmetric F → Dia F (MC F D) w → MC F D w

inductive World where
  | left | middle | right
  deriving DecidableEq, Repr

/-- Reflexive symmetric two-hop chain, with no left-to-right edge. -/
def chain : Model World Unit where
  worlds := [.left, .middle, .right]
  complete := by
    intro w; cases w with
    | left => exact .head _
    | middle => exact .tail _ (.head _)
    | right => exact .tail _ (.tail _ (.head _))
  edge := fun w => match w with
    | .left => fun v => match v with
      | .left => true
      | .middle => true
      | .right => false
    | .middle => fun v => match v with
      | .left => true
      | .middle => true
      | .right => true
    | .right => fun v => match v with
      | .left => false
      | .middle => true
      | .right => true
  atom := fun w _ => match w with
    | .left => true
    | .middle => true
    | .right => false

def p : MProp World := fun w => chain.atom w () = true
def language : Domain World := expressible chain.frame chain.valuation
/-- An inventory of one atom is intentionally not the full modal language. -/
def atomsOnly : Domain World := corpusDomain (fun (_ : Unit) => p)

def Countermodels : Prop :=
  Reflexive chain.frame ∧ Symmetric chain.frame ∧ ¬ Transitive chain.frame ∧
  (∀ w, ¬ MC chain.frame allPredicates w) ∧
  (∀ w, ¬ MC chain.frame language w) ∧
  Contingent chain.frame p .middle ∧
  MC chain.frame atomsOnly .left ∧
  Dia chain.frame (MC chain.frame atomsOnly) .middle ∧
  ¬ MC chain.frame atomsOnly .middle ∧
  (¬ ∀ P, atomsOnly P → atomsOnly (Box chain.frame P)) ∧
  eval chain .middle (.diamond (.atom ())) = true ∧
  eval chain .middle (.diamond (.neg (.atom ()))) = true ∧
  witnesses chain .middle (.atom ()) = [.left, .middle] ∧
  counterexamples chain .middle (.atom ()) = [.right]

/-- Optional identity/extensionality stays distinct from language collapse. -/
def ScopeBoundary : Prop :=
  Reflexive duplicates.frame ∧ Symmetric duplicates.frame ∧
  (∀ w, MC duplicates.frame (expressible duplicates.frame duplicates.valuation) w) ∧
  (¬ MC duplicates.frame allPredicates false) ∧
  (¬ PropositionalExtensionality (expressible duplicates.frame duplicates.valuation)) ∧
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    TruthCore.Logic.ExcludedMiddle →
    (∀ P, D P → D (fun x => ¬ P x)) → PropositionalExtensionality D →
    Symmetric F → Dia F (MC F D) w → MC F allPredicates w) ∧
  Reflexive branching.frame ∧
  Dia branching.frame (MC branching.frame allPredicates) false ∧
  (¬ MC branching.frame allPredicates false) ∧ ¬ Symmetric branching.frame

/-- An isolated root and a separate two-world component. -/
def separated : Model World Unit where
  worlds := chain.worlds
  complete := chain.complete
  edge := fun w => match w with
    | .left => fun v => match v with
      | .left => true
      | .middle => false
      | .right => false
    | .middle => fun v => match v with
      | .left => false
      | .middle => true
      | .right => true
    | .right => fun v => match v with
      | .left => false
      | .middle => true
      | .right => true
  atom := chain.atom

/-- Root-relative full collapse does not collapse disconnected components. -/
def DisconnectedScope : Prop :=
  Reflexive separated.frame ∧ Symmetric separated.frame ∧
  MC separated.frame allPredicates .left ∧
  Dia separated.frame (MC separated.frame allPredicates) .left ∧
  Box separated.frame (MC separated.frame allPredicates) .left ∧
  (World.left ≠ World.middle) ∧
  (¬ separated.frame.access .left .middle) ∧
  Contingent separated.frame p .middle

def report : String := reprStr (chain.worlds.map (fun w =>
  (w, chain.worlds.map (fun v => (v, chain.edge w v)),
   eval chain w (.atom ()), eval chain w (.box (.atom ())),
   witnesses chain w (.atom ()), counterexamples chain w (.atom ()))))
end TruthCore.Modal.BResearch
