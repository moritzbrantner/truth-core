import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Logic.ExcludedMiddle

/-! An analyst configuration related to the A8 source readings, not a binding
of those broad readings. Reuse AFP's constant-domain Property/Box/Dia. The
classifier is arbitrary except for the explicit backward-closure premise;
no deficiency-property domain or existential classifier definition is chosen.
Possible exemplification is not actual existence, an Ontic necessary bearer,
or God. Source correspondence and the evaluative inputs remain OPEN. -/
namespace TruthCore.Modal.LimitationPossibility
open TruthCore.Isabelle.AFP.GoedelGod

/-- At the selected world the supplied classifier marks Q limiting. -/
def KnownLimitingAt {W B : Type} (L : Property W B → W → Prop)
    (Q : Property W B) (w : W) : Prop := L Q w

/-- At the SAME world the supplied classifier does not mark Phi limiting. -/
def NonlimitingAt {W B : Type} (L : Property W B → W → Prop)
    (Phi : Property W B) (w : W) : Prop := ¬ L Phi w

/-- Backward closure at one standpoint, under ordinary boxed universal
property inclusion. This is an explicit input, not Scott A1a, a frame law,
or a definition that selects full uniform-deficiency semantics. -/
def BackwardClosedAt {W B : Type} (F : Frame W)
    (L : Property W B → W → Prop) (w : W) : Prop :=
  ∀ Phi Psi : Property W B,
    Box F (fun v => ∀ x, Phi x v → Psi x v) w → L Psi w → L Phi w

/-- Some accessible world has a bearer of the SAME supplied property.
No actualist existence predicate or rigid necessary individual is supplied. -/
def PossiblyExemplifiedAt {W B : Type} (F : Frame W)
    (Phi : Property W B) (w : W) : Prop := Dia F (fun v => ∃ x, Phi x v) w

/-- One world, two candidates; no metaphysical or empirical claim. -/
def controlFrame : Frame Unit := ⟨fun _ _ => True⟩

/-- A NEW formal classifier: limiting means unexemplified at this world.
It is not attributed as the source's full deficiency semantics. -/
def controlLimitation (Phi : Property Unit Bool) (w : Unit) : Prop :=
  ¬ ∃ x, Phi x w

def controlTarget : Property Unit Bool := fun x _ => x = true

def controlKnown : Property Unit Bool := fun _ _ => False

/-- Nonlimitation is just a classifier to test against Scott A1a, not a
semantic identification with Scott positivity. -/
def controlPositive : Positivity Unit Bool :=
  fun Phi w => ¬ controlLimitation Phi w

/-- SAME-model joint background and two nonlimiting complementary properties,
with possible witnesses and failure of Scott's global complement exclusion.
Explicit EM is supplied by the result that derives target possibility. -/
def JointControl : Prop :=
  KnownLimitingAt controlLimitation controlKnown () ∧
  NonlimitingAt controlLimitation controlTarget () ∧
  BackwardClosedAt controlFrame controlLimitation () ∧
  NonlimitingAt controlLimitation (fun x w => ¬ controlTarget x w) () ∧
  PossiblyExemplifiedAt controlFrame controlTarget () ∧
  PossiblyExemplifiedAt controlFrame (fun x w => ¬ controlTarget x w) () ∧
  ¬ NegationPositiveExcludesPositive controlPositive
end TruthCore.Modal.LimitationPossibility
