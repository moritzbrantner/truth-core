import TruthCore.Explanation.HistorySelection

/-! #753: the explanatory relocation test for temporal state paths.

A path assigns one state to each time inside ONE history. Worlds index rival
complete paths; time and modal accessibility stay separate parameters. No
aggregate being, causal relation, grounding relation or actual law is
introduced: `Causes` is empty in `pathHistory`, a `Constraint` is a mathematical
condition on complete paths, and a "law" is a local condition on adjacent states.
Whether any such condition governs anything is OPEN. See
`docs/notes/explanatory-relocation-753.md`. -/
namespace TruthCore.Explanation.PathRelocation
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive
open TruthCore.Explanation.HistorySelection

/-- A reindexing of time preserves a condition on complete paths. This can be
any condition, local or global; nothing requires that it be a recurrence. -/
def InvariantUnder (σ : T → T) (C : (T → S) → Prop) : Prop :=
  ∀ f, C f → C (f ∘ σ)

/-- Invariance under moving every date one step on the bi-infinite integers. -/
def ShiftInvariant (C : (Int → S) → Prop) : Prop :=
  InvariantUnder (fun t : Int => t + 1) C

/-- Exactly the paths meeting the condition; `f` is the only one. -/
def UniqueSolution (C : (T → S) → Prop) (f : T → S) : Prop :=
  C f ∧ ∀ g, C g → g = f

/-- At some time the state differs from the next state. Identity of state values
only: no passage, A-series change or causal production is encoded. -/
def Changes (f : Int → S) : Prop := ∃ t, f (t + 1) ≠ f t

/-- Local transition law: each adjacent pair of states satisfies the condition
for its time. It may be partial or many-valued, hence permits branching. -/
def Follows (R : Int → S → S → Prop) (f : Int → S) : Prop :=
  ∀ t, R t (f t) (f (t + 1))

/-- The law's condition does not depend on the date. -/
def Autonomous (R : Int → S → S → Prop) : Prop := ∀ t, R (t + 1) = R t

/-- Two paths are the same sequence up to one common re-dating. This is the
undated profile a relational view of time would use; it is not asserted here. -/
def SameUpToDating (f g : Int → S) : Prop := ∃ k, ∀ t, g t = f (t + k)

/-- Rival worlds are exactly the condition's solutions, all mutually accessible;
exactly the path's state is present at each time. `Causes` is empty, and
accessibility is an analyst's rival set, not metaphysical possibility or travel. -/
def pathHistory (C : (Int → S) → Prop) : History {g // C g} S Int where
  ontic := { frame := ⟨fun _ _ => True⟩
             ExistsAt := fun w x => x = w.1 0
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => x = w.1 t
  now := 0

/-- The same path re-dated by one step, as a rival world. -/
def shiftWorld {C : (Int → S) → Prop} (hC : ShiftInvariant C) (a : {g // C g}) :
    {g // C g} := ⟨a.1 ∘ (fun t : Int => t + 1), hC a.1 a.2⟩

/-- The token reason for one local transition: at time t the path has state s
and next state s'. These dated tokens are what "each step is explained by its
predecessor" supplies, in contrast to the law's undated condition. -/
def transitionTruth {C : (Int → S) → Prop} (w : {g // C g}) (r : Int × S × S) : Prop :=
  w.1 r.1 = r.2.1 ∧ w.1 (r.1 + 1) = r.2.2

/-- A time-indexed law read off one path; a dated copy of the explanandum. -/
def copyLaw (f : Int → S) (t : Int) (s s' : S) : Prop :=
  s = f t ∧ s' = f (t + 1)

/-- The undated law read off one path: exactly its adjacent state pairs. -/
def graphLaw (f : Int → S) (s s' : S) : Prop :=
  ∃ t, s = f t ∧ s' = f (t + 1)

/-- Actual adjacent occurrences WITHIN one path, tagged by date. This is temporal
adjacency only, not causation; it relates no two worlds. -/
def TemporalEdge (f : Int → S) (x y : Int × S) : Prop :=
  x.2 = f x.1 ∧ y.2 = f y.1 ∧ y.1 = x.1 + 1

/-- A path on the finite window 0..n under an undated state relation. -/
def FollowsFin (r : S → S → Prop) (f : Fin (n + 1) → S) : Prop :=
  ∀ i : Fin n, r (f i.castSucc) (f i.succ)

/-- Splice: f through t₀, then g. -/
def splice (f g : Int → S) (t₀ : Int) (t : Int) : S := if t ≤ t₀ then f t else g t

/-- General relocation constraints. No adequate-explanation predicate occurs.
Symmetry transfer; bi-infinite stationarity of invariant uniqueness; composition
with #736's whole-vector exclusion; exact re-encoding by transition tokens; dated
and undated law copies; a real restriction by functional autonomy; boundary
parametrization on finite windows; splicing at a shared state; and acyclicity of
dated occurrences. -/
def Certificate : Prop :=
  -- Any time reindexing preserving a condition fixes its unique solution.
  (∀ (T S : Type) (σ : T → T) (C : (T → S) → Prop) (f : T → S),
    InvariantUnder σ C → UniqueSolution C f → f ∘ σ = f) ∧
  -- Bi-infinite: a shift-invariant condition, local or global, with a unique
  -- solution has a stationary one.
  (∀ (S : Type) (C : (Int → S) → Prop) (f : Int → S),
    ShiftInvariant C → UniqueSolution C f → ¬ Changes f ∧ ∀ t, f t = f 0) ∧
  -- A date-independent local law is shift-invariant, so the same applies.
  (∀ (S : Type) (R : Int → S → S → Prop) (f : Int → S),
    Autonomous R → UniqueSolution (Follows R) f → ¬ Changes f) ∧
  -- A law periodic in time passes every period to its unique solution.
  (∀ (S : Type) (R : Int → S → S → Prop) (f : Int → S) (k : Int),
    (∀ t, R (t + k) = R t) → UniqueSolution (Follows R) f →
      ∀ t, f (t + k) = f t) ∧
  -- #738's beginningless global law is shift-invariant.
  (ShiftInvariant GlobalLaw ∧ UniqueSolution GlobalLaw fixedSignal ∧
    ¬ Changes fixedSignal) ∧
  -- A changing solution of a shift-invariant condition: any vector agreeing
  -- with its re-dating determines nothing and admits no evidence-only selector.
  (∀ (S R : Type) (C : (Int → S) → Prop) (hC : ShiftInvariant C)
      (a : {g // C g}) (truth : {g // C g} → R → Prop) (basis : R → Prop),
    Changes a.1 → SameEvidence truth basis (shiftWorld hC a) a →
      ¬ Determines (pathHistory C) truth basis a ∧
      ¬ ∃ p, EvidenceOnly truth basis p ∧ Selects (pathHistory C) p a) ∧
  -- Hence determining such a path forces a reason varying under re-dating.
  (∀ (S R : Type) (C : (Int → S) → Prop) (hC : ShiftInvariant C)
      (a : {g // C g}) (truth : {g // C g} → R → Prop) (basis : R → Prop),
    Changes a.1 → Determines (pathHistory C) truth basis a →
      ∃ r, basis r ∧ ¬ (truth (shiftWorld hC a) r ↔ truth a r)) ∧
  -- With world-invariant truth (a law held fixed), determination holds exactly
  -- when the condition has only the actual solution.
  (∀ (S R : Type) (C : (Int → S) → Prop) (a : {g // C g}) (P : R → Prop)
      (basis : R → Prop),
    Determines (pathHistory C) (fun _ r => P r) basis a ↔ ∀ g, C g → g = a.1) ∧
  -- Transition tokens carry exactly the path: same evidence is same history, so
  -- they determine it and every evidence-only selector is coextensive with it.
  (∀ (S : Type) (C : (Int → S) → Prop) (a v : {g // C g}),
    (SameEvidence transitionTruth (fun _ => True) v a ↔
      SameHistory (pathHistory C) v a) ∧
    Determines (pathHistory C) transitionTruth (fun _ => True) a ∧
    ∀ p, EvidenceOnly transitionTruth (fun _ => True) p →
      Selects (pathHistory C) p a → (p v ↔ SameHistory (pathHistory C) v a)) ∧
  -- Every dated path is the unique solution of its own time-indexed copy law,
  -- and these laws differ exactly when the paths do.
  (∀ (S : Type) (f g : Int → S),
    UniqueSolution (Follows (copyLaw f)) f ∧ (copyLaw f = copyLaw g ↔ f = g)) ∧
  -- Every never-repeating path is selected up to dating by its own undated graph
  -- law, and these laws agree exactly when the paths agree up to dating.
  (∀ (S : Type) (f g : Int → S), Function.Injective f →
    Follows (fun _ => graphLaw f) f ∧
    (Follows (fun _ => graphLaw f) g → SameUpToDating f g) ∧
    (Function.Injective g → (graphLaw f = graphLaw g ↔ SameUpToDating f g))) ∧
  -- Functional undated laws DO exclude: no solution revisits a state and then
  -- continues differently.
  (∀ (S : Type) (r : S → S → Prop) (f : Int → S) (t u : Int),
    (∀ s a b, r s a → r s b → a = b) → Follows (fun _ => r) f →
      f t = f u → f (t + 1) = f (u + 1)) ∧
  -- Finite window, total functional law: the start state parametrizes solutions.
  (∀ (S : Type) (n : Nat) (step : S → S),
    Function.Bijective (fun f : {f : Fin (n + 1) → S //
      FollowsFin (fun a b => b = step a) f} => f.1 0)) ∧
  -- Solutions meeting at a state splice into a solution of the same law.
  (∀ (S : Type) (R : Int → S → S → Prop) (f g : Int → S) (t₀ : Int),
    Follows R f → Follows R g → f t₀ = g t₀ → Follows R (splice f g t₀)) ∧
  -- Dated occurrences of one path form no cycle, and each has a predecessor.
  (∀ (S : Type) (f : Int → S),
    (∀ x, ¬ Relation.TransGen (TemporalEdge f) x x) ∧
    ∀ t, TemporalEdge f (t - 1, f (t - 1)) (t, f t))

/-! Concrete fixtures. Bool values are abstract state labels. -/

/-- Alternation: the state differs from its predecessor; total and functional. -/
def flip (s s' : Bool) : Prop := s' = !s

def alt (t : Int) : Bool := decide (t % 2 = 0)

/-- One extra dated condition breaks the shift symmetry. -/
def pinned (f : Int → Bool) : Prop := Follows (fun _ => flip) f ∧ f 0 = true

/-- A shift-invariant condition with a stationary unique solution. -/
def allTrue (f : Int → Bool) : Prop := ∀ t, f t = true

/-- Undated many-valued law: false may stay or turn true; true stays true. -/
def rise (s s' : Bool) : Prop := s = true → s' = true

def stayFalse (_ : Int) : Bool := false
def riseAtOne (t : Int) : Bool := decide (0 < t)

/-- Only the past and present transition tokens are admitted. -/
def upToNow (r : Int × Bool × Bool) : Prop := r.1 < 0

/-- Revisits `true` and continues differently. -/
def revisit (t : Int) : Bool := decide (t = 0 ∨ t = 1)

/-- Finite-window relations with one edge, in opposite directions. -/
def onlyTF (a b : Bool) : Prop := a = true ∧ b = false
def onlyFT (a b : Bool) : Prop := a = false ∧ b = true

/-- Witnesses and omission controls for `Certificate`, one fixture per clause:
a changing beginningless path unique up to dating; its failure and success under
law-level and token vectors; dating as the only rival; pinning as a dated selector
breaking invariance; a stationary law control; a branching law with a shared past;
a path a functional undated law excludes and its dated copy selects; finite windows where an
undated law alone selects a changing path; and a state cycle with no dated cycle. -/
def Controls : Prop :=
  -- Flip: beginningless and changing, exactly the alternation and its re-dating.
  (Follows (fun _ => flip) alt ∧ Changes alt ∧
    Autonomous (fun _ : Int => flip) ∧
    (∀ g, Follows (fun _ => flip) g → g = alt ∨ g = alt ∘ (fun t : Int => t + 1)) ∧
    (∀ g, Follows (fun _ => flip) g → SameUpToDating alt g) ∧
    alt ∘ (fun t : Int => t + 1) ≠ alt) ∧
  -- Undated law facts fail for the dated contrast; transition tokens succeed.
  (∀ a : {g // Follows (fun _ => flip) g},
    ¬ Determines (pathHistory (Follows (fun _ => flip)))
        (fun _ (_ : Unit) => True) (fun _ => True) a ∧
    Determines (pathHistory (Follows (fun _ => flip)))
        transitionTruth (fun _ => True) a) ∧
  -- Invariance is indispensable: one dated pin gives a changing unique solution.
  (UniqueSolution pinned alt ∧ Changes alt ∧ ¬ ShiftInvariant pinned) ∧
  -- Changing is indispensable: a stationary unique solution is determined by
  -- world-invariant truth despite invariance.
  (ShiftInvariant allTrue ∧ UniqueSolution allTrue (fun _ => true) ∧
    ¬ Changes (fun _ : Int => true) ∧
    ∀ a : {g // allTrue g},
      Determines (pathHistory allTrue) (fun _ (_ : Unit) => True) (fun _ => True) a) ∧
  -- Branching: one autonomous law, shared past, different continuations; past
  -- tokens do not determine, and all tokens do.
  (Follows (fun _ => rise) stayFalse ∧ Follows (fun _ => rise) riseAtOne ∧
    (∀ t, t ≤ 0 → stayFalse t = riseAtOne t) ∧ stayFalse 1 ≠ riseAtOne 1 ∧
    ∀ h : Follows (fun _ => rise) stayFalse,
      ¬ Determines (pathHistory (Follows (fun _ => rise)))
          transitionTruth upToNow ⟨stayFalse, h⟩) ∧
  -- A functional undated law excludes this path; its dated copy selects it.
  ((∀ r : Bool → Bool → Prop, (∀ s a b, r s a → r s b → a = b) →
      ¬ Follows (fun _ => r) revisit) ∧
    UniqueSolution (Follows (copyLaw revisit)) revisit) ∧
  -- Finite window: an undated law alone uniquely selects a changing path, with
  -- the swapped law selecting its rival; impossible for a bi-infinite path.
  ((∃ f : Fin 2 → Bool, UniqueSolution (FollowsFin onlyTF) f ∧ f 1 ≠ f 0 ∧
      ∃ g : Fin 2 → Bool, UniqueSolution (FollowsFin onlyFT) g ∧ g ≠ f)) ∧
  -- State arrows form a 2-cycle; alternatives are mutually accessible; dated
  -- occurrences stay acyclic, and every one of them has a predecessor.
  ((flip true false ∧ flip false true) ∧
    (∀ v w : {g // Follows (fun _ => flip) g},
      (pathHistory (Follows (fun _ => flip))).ontic.frame.access v w) ∧
    (∀ x, ¬ Relation.TransGen (TemporalEdge alt) x x) ∧
    ∀ t, TemporalEdge alt (t - 1, alt (t - 1)) (t, alt t))

end TruthCore.Explanation.PathRelocation
