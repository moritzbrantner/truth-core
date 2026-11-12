module

public import TruthCore.Causality.ComingToBeHorns
public import TruthCore.Causality.BegunComingToBe

/-!
# A Grim Reaper patchwork premise over the moments of a history

Analyst formulation for the modal spine to "God exists"
(`docs/notes/modal-spine.md`, premises A3′a and A3′w), in the style of the
Koons/Pruss Grim Reaper argument as reconstructed in
`docs/notes/causal-finitism-367.md` (possible local Placer patches, room in an
alleged infinite past, causal-network patchwork). Attribution deferred: nothing
here is claimed to be Koons's or Pruss's exact principle.

It replaces the near-transcription `ComingToBeHorns.ReaperAssembly`, whose
consequent was a closed claim about `Nat` functions. Here the stations sit *at
the moments* of a strictly descending sequence `c` of moments of a history, in
worlds of that history, and the premise has two independent parts:

* **Local pieces** (`ReaperPiecesPossible`): along every descent below a
  populated moment, each two adjacent stations, with their local rules, are
  realized together in some accessible world. This is the analogue of a
  possible Placer trio placed in the slots of that descent.
* **Patchwork** (`ReaperPatchwork`): along every such descent, if each adjacent
  pair of pieces is co-possible, some accessible world realizes all pieces at
  once. This is the countable gluing step.

Neither part mentions foundedness, and each holds without the other in a
beginningless history (`Control.Certificate`). The derivation translates a
glued world's registers into a `Nat`-indexed signal system and composes the
verified `IndexedSignalReaper.impossible`. Because that impossibility is a
theorem, the typed patchwork premise for a given frame says no more than "along
every populated descent, adjacent pieces are not all co-possible", and founded
populated pasts are equivalent to the two premises together (for any frame).
The split is still informative: each part is motivated separately, and the
warrant for patchwork must come from the general recombination principle it
instantiates, not from this instance.

**Vocabulary.** A `ReaperFrame` gives, at each world `u` and moment `t`, the
code on the output register of the station at `t` (`out u t`, absent or a
moment naming the issuing station) and whether that station issues
(`issues u t`). The four rules of station `n` of a descent `c`, whose
immediately upstream (earlier) station sits at `c (n + 1)`:

1. positive trigger: no upstream code → the station issues;
2. emission: issuing writes the station's own code `c n`;
3. forwarding: an upstream code is copied unchanged;
4. admissibility: every code on the station's output names a station of the
   same descent at or upstream of it (`c j` with `n ≤ j`).

Rules 1–3 relate only the registers at `c n` and `c (n + 1)`. Rule 4 constrains
only the register at `c n`, but refers to every upstream slot of the whole
descent, so a piece is not local in the descent: it is the clause that excludes
a code from a source outside the descent, for instance one at the accumulation
point `0` of `t, t/2, …` in `[0, t]`, which is exactly where `[0, t]` and
`(0, t]` differ.

The registers are an extensional record of what the stations do in the world;
the rules hold in that world. They are not tied to the history's `ExistsAt` or
`IsAt`, so a piece has no existential import (the controls realize a pair of
pieces in a world where nothing exists). No counterfactual, causal power,
intrinsicality or concrete station is encoded: those are the reasons offered
*for* the local and patchwork premises, and the bridge from recombining
concrete stations to these typed register premises is not built.

**Two strengths.** The unrestricted premises range over every descent below a
populated moment, and give founded populated pasts (`Acc`, A3′a). That also
excludes contingent presence after the first moment of a dense past with a
beginning (the dense, first-moment setting of Benardete-style paradoxes), where
`t, t/2, t/4, …` is a descent. The coinitial premises range only over descents
that run below every earlier moment of the populated one (`Coinitial`), e.g.
one station per past day where the past is metrically infinite. Such a descent
exists only where the past has no beginning, so they give begun populated pasts
(`BegunAt`) given that every beginningless populated past has a coinitial
descent (`BeginninglessPastsCountablyCoinitial`: checked for integer times;
the full rational or real line by `t - n`, an open-below half-line such as
`(0, ∞)` by `t / 2 ^ n`). `Coinitial` is purely order-theoretic: `(0, t]` and
`(-∞, t]` are order-isomorphic, so a coinitial descent may accumulate
metrically, and the coinitial premises apply equally to a metrically finite past
with no first moment, such as that of standard FLRW cosmology (where the
singularity is not a moment). The unrestricted premises imply the coinitial ones.

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.GrimReaperPatchwork

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.BegunComingToBe

/-- Station registers of a history's worlds: `out u t` is the code (absent, or
a moment naming the issuing station) on the output register of the station at
moment `t` in world `u`; `issues u t` says that station issues its own code. -/
structure ReaperFrame (W T : Type) where
  out : W → T → Option T
  issues : W → T → Prop

/-- `c` is a strictly descending sequence of moments. -/
def Descent {T : Type} [Preorder T] (c : Nat → T) : Prop :=
  ∀ n, c (n + 1) < c n

/-- The descent runs below every moment earlier than its first member. -/
def Coinitial {T : Type} [Preorder T] (c : Nat → T) : Prop :=
  ∀ s, s < c 0 → ∃ n, c n < s

/-- Some contingent concrete individual is present at `t` in world `v`. -/
def PopulatedAt {W B T : Type} (h : History W B T) (Concrete : B → Prop)
    (v : W) (t : T) : Prop :=
  ∃ x, Concrete x ∧ ContingentAt h.ontic v x ∧ h.IsAt v x t

/-- The piece of station `n` of descent `c` in world `u`: its positive trigger,
emission and forwarding rules, relative to the station at `c (n + 1)`
immediately upstream, and its admissibility rule, which constrains only the
register at `c n` but refers to every upstream slot `c j` (`n ≤ j`) of the
descent. -/
def PieceAt {W T : Type} (R : ReaperFrame W T) (u : W) (c : Nat → T) (n : Nat) :
    Prop :=
  (R.out u (c (n + 1)) = none → R.issues u (c n)) ∧
  (R.issues u (c n) → R.out u (c n) = some (c n)) ∧
  (∀ r, R.out u (c (n + 1)) = some r → R.out u (c n) = some r) ∧
  (∀ r, R.out u (c n) = some r → ∃ j, n ≤ j ∧ r = c j)

/-- Along `c`, every two adjacent pieces are realized together in some world
accessible from `v` (pairwise local compatibility). -/
def AdjacentPiecesCoPossible {W B T : Type} (R : ReaperFrame W T)
    (h : History W B T) (v : W) (c : Nat → T) : Prop :=
  ∀ n, ∃ u, h.ontic.frame.access v u ∧ PieceAt R u c n ∧ PieceAt R u c (n + 1)

/-- Some world accessible from `v` realizes every piece along `c`. -/
def ArrangementPossible {W B T : Type} (R : ReaperFrame W T)
    (h : History W B T) (v : W) (c : Nat → T) : Prop :=
  ∃ u, h.ontic.frame.access v u ∧ ∀ n, PieceAt R u c n

/-- Local Reaper pieces, unrestricted: in every history `v` accessible from
`w`, along every strictly descending sequence of moments starting at a
populated moment, every two adjacent pieces are co-possible. -/
def ReaperPiecesPossible {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, Descent c →
    PopulatedAt h Concrete v (c 0) → AdjacentPiecesCoPossible R h v c

/-- Reaper patchwork, unrestricted: in every history `v` accessible from `w`,
along every strictly descending sequence of moments starting at a populated
moment, if every two adjacent pieces are co-possible, the whole arrangement is
possible. -/
def ReaperPatchwork {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, Descent c →
    PopulatedAt h Concrete v (c 0) →
    AdjacentPiecesCoPossible R h v c → ArrangementPossible R h v c

/-- Local Reaper pieces along coinitial descents only. -/
def CoinitialReaperPiecesPossible {W B T : Type} [Preorder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop) (w : W) :
    Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, Descent c → Coinitial c →
    PopulatedAt h Concrete v (c 0) → AdjacentPiecesCoPossible R h v c

/-- Reaper patchwork along coinitial descents only. -/
def CoinitialReaperPatchwork {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, Descent c → Coinitial c →
    PopulatedAt h Concrete v (c 0) →
    AdjacentPiecesCoPossible R h v c → ArrangementPossible R h v c

/-- In every history accessible from `w`, every populated moment whose past has
no beginning starts a coinitial descent (countable coinitiality of
beginningless populated pasts). -/
def BeginninglessPastsCountablyCoinitial {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ t, PopulatedAt h Concrete v t → ¬ BegunAt t →
    ∃ c : Nat → T, c 0 = t ∧ Descent c ∧ Coinitial c

/-- In every history accessible from `w`, every moment at which some contingent
concrete individual is present has a past with a beginning. This denies the
begun version of horn H2 for every accessible history in which a contingent
concrete thing is present at all. -/
def PopulatedPastsBegun {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ x t, Concrete x → ContingentAt h.ontic v x →
    h.IsAt v x t → BegunAt t

namespace Control

/-- Integer worlds, individuals and times, every world accessible from every
world. At every world other than `0` every individual exists, and individual
`n` is present at every time `t ≥ n`; nothing exists at world `0`. -/
def pivot : History Int Int Int where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w _ => w ≠ 0,
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => w ≠ 0 ∧ x ≤ t
  now := 0

/-- No register ever carries a code and no station issues. -/
def quietFrame (W T : Type) : ReaperFrame W T where
  out := fun _ _ => none
  issues := fun _ _ => False

/-- World `k`: stations before `k` carry no code, the station at `k` issues
its own code, and every later station carries code `k`. -/
def pivotFrame : ReaperFrame Int Int where
  out := fun k t => if t < k then none else some k
  issues := fun k t => t = k

open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Causality.BegunComingToBe.Control (zeno predecessorGrounds)

/-- Independence and nonvacuity controls, every individual counted concrete:
(1) in the beginningless integer history `pivot` with silent registers, both
patchwork premises hold, neither local-pieces premise holds, and populated pasts
are neither founded nor begun;
(2) in `pivot` with the pivot registers, both local-pieces premises hold, both
patchwork premises fail, populated pasts are not begun, and beginningless
populated pasts are countably coinitial;
(3) in `BegunComingToBe.Control.zeno` (a first moment followed by moments with
no earliest one) with silent registers: the coinitial local-pieces and
patchwork premises, countable coinitiality, begun populated pasts and the
earlier-grounded possibility premise all hold, begun coming-to-be is possible,
no concrete individual is necessary at either world, populated pasts are not
founded, and for every register frame the unrestricted local-pieces and
patchwork premises do not both hold. -/
def Certificate : Prop :=
  (ReaperPatchwork (quietFrame Int Int) pivot all 1 ∧
    CoinitialReaperPatchwork (quietFrame Int Int) pivot all 1 ∧
    ¬ ReaperPiecesPossible (quietFrame Int Int) pivot all 1 ∧
    ¬ CoinitialReaperPiecesPossible (quietFrame Int Int) pivot all 1 ∧
    ¬ ComingToBeHorns.PopulatedPastsFounded pivot all 1 ∧
    ¬ PopulatedPastsBegun pivot all 1) ∧
  (ReaperPiecesPossible pivotFrame pivot all 1 ∧
    CoinitialReaperPiecesPossible pivotFrame pivot all 1 ∧
    ¬ ReaperPatchwork pivotFrame pivot all 1 ∧
    ¬ CoinitialReaperPatchwork pivotFrame pivot all 1 ∧
    ¬ PopulatedPastsBegun pivot all 1 ∧
    BeginninglessPastsCountablyCoinitial pivot all 1) ∧
  (CoinitialReaperPiecesPossible (quietFrame Bool (WithBot Int)) zeno all true ∧
    CoinitialReaperPatchwork (quietFrame Bool (WithBot Int)) zeno all true ∧
    BeginninglessPastsCountablyCoinitial zeno all true ∧
    PopulatedPastsBegun zeno all true ∧
    ComingToBeHorns.PossiblyEarlierGroundedPopulated zeno all predecessorGrounds true ∧
    PossiblyBegunComingToBe zeno all true ∧
    (∀ v, ¬ TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt
      ⟨zeno.ontic, all, predecessorGrounds⟩ v) ∧
    ¬ ComingToBeHorns.PopulatedPastsFounded zeno all true ∧
    ∀ R : ReaperFrame Bool (WithBot Int),
      ¬ (ReaperPiecesPossible R zeno all true ∧ ReaperPatchwork R zeno all true))

end Control

end TruthCore.Causality.GrimReaperPatchwork
