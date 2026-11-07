module

public import TruthCore.Causality.NecessaryClassicalGodRoot
public import TruthCore.Causality.Round2Grounding
public import TruthCore.Modal.Cube
public import TruthCore.Isabelle.AFP.GoedelGod
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia

/-!
# Sense fork over "necessary" in the necessary-classical-God route

Analyst formulation, attribution deferred (owner direction on the modal task,
2026-11-07). The necessary-being route (`NECESSARY-CLASSICAL-GOD-ROOT`) states
the necessity of its root with `NecessaryAt m.ontic w n`, which is literally
the Kripke box of `TruthCore.Modal.Kripke` applied to the atom "n exists",
over the frame `m.ontic.frame` (`necessaryAt_iff_boxExistsAt`, proved by
`Iff.rfl`: no bridge premise identifies the two).

`Sense` lists the defensible readings of "necessary being" that the corpus
already defines (`DISAMB-NECESSARY`). `NecessaryIn` unfolds each constructor to
the existing declaration of that sense:

* `boxK`: possibilist de re box-existence, `Holds frame V w (□ atom x)`, frame
  class K (no frame condition; `DEF-KANT-MODAL-NECESSITY`,
  `DEF-MODAL-FIXTURE-FRAME`);
* `actualistK`: the same box with an actual witness (`x` exists at `w`), the
  actualist reading of the outer quantifier (`Ontic.NecessaryBeing`);
* `deDictoK`: de dicto, `Box frame (∃ y, y exists) w`: necessarily something
  exists (`DEF-QML-KB-NECESSITY` box, actualist inner quantifier); it does
  not attach necessity to `x`;
* `boxT`, `boxS4`, `boxB`, `boxS5`: possibilist de re box-existence read in
  the frame class KT, S4, KTB, S5 (`TruthCore.Modal.FrameSatisfies`): the frame
  condition is part of the reading;
* `tertiaVia`: `IsNecessary` of ST I q.2 a.3 ("cannot not-be",
  `DEF-NECESSARY-BEING`) with its primitive possibility read as the frame's
  diamond `Dia frame · w`;
* `perSe`: `IsNecessaryPerSe` (`DEF-NECESSARY-PER-SE`) under the same
  possibility, with a supplied relation "c causes the necessity of x".

Not in the enum (recorded in `DISAMB-NECESSARY` as unresolved): logical
necessity (`DEF-LOGICAL-NECESSITY`, said of propositions; no Lean declaration)
and the essence-based Scott, Goedel-1970 and filtered `NecessaryExistence`
(the route supplies no essences).

The worlds of `m.ontic.frame` are complete possible histories (as in
`BruteFoundationBoundary`); necessity here is neither eternity nor
immutability (#469).
-/

@[expose] public section

namespace TruthCore.Causality.NecessarySenseFork

open TruthCore.Modal
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.Round2Grounding
  (NecessityCauseRelataActualConcrete NecessitatedDependsOnItsCause ActualDependenceIsGrounding)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsNecessary IsNecessaryPerSe)
open TruthCore.Case.Catholicism (Signature IsTheOneGod)

variable {W B : Type}

/-! ## Kripke vocabulary for existence -/

/-- The existence valuation: the atom `x` holds at `v` iff `x` exists at `v`.
Atoms are rigid candidate individuals, so `□ atom x` is de re necessity of
that same individual (`DEF-MODAL-FIXTURE-FRAME`). -/
def existenceValuation (o : Ontic W B) : Valuation W B := fun v x => o.ExistsAt v x

/-- Box-existence in the Kripke semantics of `TruthCore.Modal.Kripke`:
`x` exists at every world accessible from `w` in `o.frame`. -/
def BoxExistsAt (o : Ontic W B) (w : W) (x : B) : Prop :=
  Holds o.frame (existenceValuation o) w (.box (.atom x))

/-- The route's necessity IS the Kripke box: definitional, no bridge. -/
theorem necessaryAt_iff_boxExistsAt (o : Ontic W B) (w : W) (x : B) :
    NecessaryAt o w x ↔ BoxExistsAt o w x := Iff.rfl

/-- Contingency is `atom ∧ ◇¬atom` in the same semantics. -/
theorem contingentAt_iff_holds (o : Ontic W B) (w : W) (x : B) :
    ContingentAt o w x ↔
      Holds o.frame (existenceValuation o) w (.atom x) ∧
      Holds o.frame (existenceValuation o) w (.diamond (Formula.neg (.atom x))) := Iff.rfl

/-- The tertia via's primitive possibility read as the frame's diamond at `w`. -/
def FramePossible (o : Ontic W B) (w : W) : (W → Prop) → Prop :=
  fun C => TruthCore.Isabelle.AFP.GoedelGod.Dia o.frame C w

/-- World-indexed existence as the tertia via's `IsAt` (times read as worlds). -/
def ExistsIndexed (o : Ontic W B) : B → W → Prop := fun x v => o.ExistsAt v x

/-! ## The sense enum and the sense-relative predicate -/

/-- Defensible readings of the route's "necessary being". Finite, so
exhaustiveness of the enum itself is free; that the intended reading is one
of them is the separate coverage premise `NecessaryReadingCovered`. -/
inductive Sense where
  | boxK
  | actualistK
  | deDictoK
  | boxT
  | boxS4
  | boxB
  | boxS5
  | tertiaVia
  | perSe
  deriving DecidableEq, Repr

/-- The sense-relative necessary-being predicate, by cases on the sense.
`CausesNecessityOf c x` ("c causes the necessity of x") is used only by `perSe`. -/
def NecessaryIn (s : Sense) (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (x : B) : Prop :=
  match s with
  | .boxK => BoxExistsAt m.ontic w x
  | .actualistK => m.ontic.ExistsAt w x ∧ BoxExistsAt m.ontic w x
  | .deDictoK =>
      TruthCore.Isabelle.AFP.GoedelGod.Box m.ontic.frame (fun v => ∃ y, m.ontic.ExistsAt v y) w
  | .boxT => FrameSatisfies .KT m.ontic.frame ∧ BoxExistsAt m.ontic w x
  | .boxS4 => FrameSatisfies .S4 m.ontic.frame ∧ BoxExistsAt m.ontic w x
  | .boxB => FrameSatisfies .KTB m.ontic.frame ∧ BoxExistsAt m.ontic w x
  | .boxS5 => FrameSatisfies .S5 m.ontic.frame ∧ BoxExistsAt m.ontic w x
  | .tertiaVia => IsNecessary (FramePossible m.ontic w) (ExistsIndexed m.ontic) x
  | .perSe =>
      IsNecessaryPerSe (FramePossible m.ontic w) (ExistsIndexed m.ontic) CausesNecessityOf x

/-- What the route says of its root besides necessity: an actual root (no
actual concrete ground), God, the one God, with the classical attributes. -/
def RootFacts (σ : Signature) (m : Profile W σ.Being) (w : W) (n : σ.Being) : Prop :=
  ActualRoot m w n ∧ σ.IsGod n ∧ IsTheOneGod σ.IsGod n ∧ σ.HasClassicalAttributes n

/-- The route's necessary-being node under sense `s`. -/
def NecessaryRootInSense (s : Sense) (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CausesNecessityOf : σ.Being → σ.Being → Prop) : Prop :=
  ∃ n, NecessaryIn s m w CausesNecessityOf n ∧ RootFacts σ m w n

/-! Per-sense nodes, one declaration per corpus statement. -/

def NecessaryRootBoxK (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .boxK σ m w CN
def NecessaryRootActualistK (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .actualistK σ m w CN
def NecessaryRootDeDictoK (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .deDictoK σ m w CN
def NecessaryRootBoxT (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .boxT σ m w CN
def NecessaryRootBoxS4 (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .boxS4 σ m w CN
def NecessaryRootBoxB (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .boxB σ m w CN
def NecessaryRootBoxS5 (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .boxS5 σ m w CN
def NecessaryRootTertiaVia (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .tertiaVia σ m w CN
def NecessaryRootPerSe (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : Prop := NecessaryRootInSense .perSe σ m w CN

/-! ## Frame-class premises (open, one per frame class) -/

/-- OPEN frame premise: the route's modal frame is reflexive (logic KT). -/
def OnticFrameKT (m : Profile W B) : Prop := FrameSatisfies .KT m.ontic.frame
/-- OPEN frame premise: the route's modal frame is reflexive and transitive (S4). -/
def OnticFrameS4 (m : Profile W B) : Prop := FrameSatisfies .S4 m.ontic.frame
/-- OPEN frame premise: the route's modal frame is reflexive and symmetric (KTB). -/
def OnticFrameKTB (m : Profile W B) : Prop := FrameSatisfies .KTB m.ontic.frame
/-- OPEN frame premise: the route's modal frame is reflexive and Euclidean (S5). -/
def OnticFrameS5 (m : Profile W B) : Prop := FrameSatisfies .S5 m.ontic.frame

/-! ## Per-sense side conditions, coverage, and the fork node -/

/-- What adopting sense `s` adds beyond the route's own inputs: the frame
condition for a frame-class reading; for `perSe`, the three Round2Grounding
premises tying causes of necessity to actual concrete grounding; nothing
otherwise. -/
def SenseSupport (s : Sense) (m : Profile W B) (w : W)
    (CausesNecessityOf DependsForBeing : B → B → Prop) : Prop :=
  match s with
  | .boxK | .actualistK | .deDictoK | .tertiaVia => True
  | .boxT => FrameSatisfies .KT m.ontic.frame
  | .boxS4 => FrameSatisfies .S4 m.ontic.frame
  | .boxB => FrameSatisfies .KTB m.ontic.frame
  | .boxS5 => FrameSatisfies .S5 m.ontic.frame
  | .perSe =>
      NecessityCauseRelataActualConcrete m w CausesNecessityOf ∧
        NecessitatedDependsOnItsCause CausesNecessityOf DependsForBeing ∧
        ActualDependenceIsGrounding m w DependsForBeing

/-- OPEN coverage premise (STMT-NECESSARY-SENSES-EXHAUSTIVE, labelled,
attribution deferred): the route's intended reading of "necessary being" is
one of the enumerated senses. Exhaustiveness of the finite enum is free; that
the enum lists every defensible reading is not provable in Lean. It is
attacked by proposing a further sense. `Intended` is the reading choice and
is otherwise unconstrained. -/
def NecessarySensesExhaustive (Intended : Sense → Prop) : Prop := ∃ s, Intended s

/-- OPEN exclusivity premise (STMT-NECESSARY-SENSE-UNIQUE, labelled,
attribution deferred): the route's intended reading selects exactly one
constructor. This is a constraint on the CHOICE of reading, not a claim that
the extensions of the senses are disjoint: they are not, since they are
strength-ordered (S5 box-existence implies S4 implies T; see the `strengthens`
relations). Disjoint cells ("box-existence in class C and in no stronger
class") were not used because the route's conclusion is monotone in strength,
so cells would only re-split the same derivations. -/
def NecessarySenseUnique (Intended : Sense → Prop) : Prop :=
  ∀ s t, Intended s → Intended t → s = t

/-- OPEN premise: whichever enumerated sense is intended, its side condition
(`SenseSupport`) holds. Trivial for K, actualist K, de dicto K and tertia via. -/
def IntendedSenseSupported (Intended : Sense → Prop) (m : Profile W B) (w : W)
    (CausesNecessityOf DependsForBeing : B → B → Prop) : Prop :=
  ∀ s, Intended s → SenseSupport s m w CausesNecessityOf DependsForBeing

/-- The fork node: the intended reading selects exactly one sense, and the
route's root is necessary in that sense and has the root facts. -/
def NecessaryRootOnIntendedReading (Intended : Sense → Prop) (σ : Signature)
    (m : Profile W σ.Being) (w : W) (CN : σ.Being → σ.Being → Prop) : Prop :=
  ∃ s, (Intended s ∧ ∀ t, Intended t → t = s) ∧ NecessaryRootInSense s σ m w CN

/-! ## Separation controls (formal, finite) -/

namespace Control

/-- Worlds are naturals; `n → n + 1` plus reflexive loops: reflexive, not
transitive (`0 → 1 → 2` without `0 → 2`). -/
def chainFrame : Frame Nat := ⟨fun a b => a = b ∨ a + 1 = b⟩

/-- One individual existing at worlds 0 and 1 only. -/
def chainOntic : Ontic Nat Unit where
  frame := chainFrame
  ExistsAt := fun v _ => v < 2
  Causes := fun _ _ _ => False

/-- Two worlds, `0 → 1` only: not reflexive at 0. -/
def stepFrame : Frame Bool := ⟨fun a b => a = false ∧ b = true⟩

/-- The individual exists at `true` only. -/
def stepOntic : Ontic Bool Unit where
  frame := stepFrame
  ExistsAt := fun v _ => v = true
  Causes := fun _ _ _ => False

/-- Universal two-world frame; individual `b` exists exactly at world `b`. -/
def swapOntic : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun v b => v = b
  Causes := fun _ _ _ => False

/-- The separation certificate:
1. on the reflexive non-transitive chain, `□E` holds at 0 but `□□E` fails
   (S4's characteristic consequence needs transitivity);
2. on the non-reflexive step frame, possibilist `□E` holds at `false` while
   the individual does not exist there (actualist and possibilist readings
   differ without reflexivity);
3. on the universal frame, de dicto `□∃y E y` holds while no individual is
   de re box-existent (de dicto does not give a de re necessary being). -/
def Certificate : Prop :=
  (BoxExistsAt chainOntic 0 () ∧
    ¬ Holds chainOntic.frame (existenceValuation chainOntic) 0 (.box (.box (.atom ())))) ∧
  (BoxExistsAt stepOntic false () ∧ ¬ stepOntic.ExistsAt false ()) ∧
  (TruthCore.Isabelle.AFP.GoedelGod.Box swapOntic.frame (fun v => ∃ y, swapOntic.ExistsAt v y) false ∧
    ¬ ∃ y, BoxExistsAt swapOntic false y)

/-- Two necessary individuals on the universal frame; `false` causes the
necessity of `true`. -/
def pairOntic : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

/-- `c` causes the necessity of `x` exactly when `c = false` and `x = true`. -/
def pairCausesNecessity (c x : Bool) : Prop := c = false ∧ x = true

/-- Per se failure: `true` is box-existent and cannot not-be (tertia via), yet
it is not necessary per se, since `false` causes its necessity. -/
def PerSeSeparation : Prop :=
  BoxExistsAt pairOntic false true ∧
  IsNecessary (FramePossible pairOntic false) (ExistsIndexed pairOntic) true ∧
  ¬ IsNecessaryPerSe (FramePossible pairOntic false) (ExistsIndexed pairOntic)
      pairCausesNecessity true

/-- A one-point signature: its one being is God and has the classical
attributes. The historical and creedal fields are unused placeholders. -/
def unitSignature : Signature where
  Being := Unit
  IsGod := fun _ => True
  HasClassicalAttributes := fun _ => True
  RevealsRecognizably := fun _ => False
  jesus := ()
  ClaimedDivineAuthority := fun _ => False
  RoseFromTheDead := fun _ => False
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => False
  VisibleWithAuthority := fun _ => False
  FoundedAsTeachingAuthority := fun _ _ => False
  DefinitivelyProposesAsRevealed := fun _ _ => False
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

/-- One world accessing itself; the one being exists there, is concrete and
ungrounded. -/
def unitProfile : Profile Unit unitSignature.Being where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Nonvacuity: in the one-point model every sense's node and every side
condition holds, and exactly one sense (`boxS5`) is intended. -/
def Nonvacuity : Prop :=
  (∀ s, NecessaryRootInSense s unitSignature unitProfile () (fun _ _ => False) ∧
    SenseSupport s unitProfile () (fun _ _ => False) (fun _ _ => False)) ∧
  NecessarySensesExhaustive (· = Sense.boxS5) ∧ NecessarySenseUnique (· = Sense.boxS5)

/-- Frame-class consequences of box-existence, from the Kripke axiom
theorems: T gives actual existence, S4 gives necessary necessity (axiom 4),
KTB gives `E → □◇E` (axiom B), S5 gives `◇□E → □E`. -/
def FrameSenseLaws : Prop :=
  ∀ (W B : Type) (o : Ontic W B) (w : W) (x : B),
    (FrameSatisfies .KT o.frame → BoxExistsAt o w x → o.ExistsAt w x) ∧
    (FrameSatisfies .S4 o.frame → BoxExistsAt o w x →
      Holds o.frame (existenceValuation o) w (.box (.box (.atom x)))) ∧
    (FrameSatisfies .KTB o.frame → o.ExistsAt w x →
      Holds o.frame (existenceValuation o) w (.box (.diamond (.atom x)))) ∧
    (FrameSatisfies .S5 o.frame →
      Holds o.frame (existenceValuation o) w (.diamond (.box (.atom x))) → BoxExistsAt o w x)

/-- The batch controls: frame laws, the three separations, the per se
separation, and the nonvacuity model. -/
def Controls : Prop := FrameSenseLaws ∧ Certificate ∧ PerSeSeparation ∧ Nonvacuity

end Control

end TruthCore.Causality.NecessarySenseFork
