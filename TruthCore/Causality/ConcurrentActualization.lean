module

public import TruthCore.Causality.SustainingCausation
public import TruthCore.Causality.DeiFiliusUnifiedRoute

/-!
# Concurrent actualization: the typed crux of the existential-inertia dispute

Analyst formulation for the modal spine (`docs/notes/modal-spine.md`).
Attribution deferred: no claim states any premise below. The reply attributed
to Feser 2021 and the rival attributed to Schmid 2021 (both read in the corpus,
passages `FESER-INERTIA-REPLY-2021-ARTICLE` and `SCHMID-INERTIA-REPLY-3-ARTICLE`)
motivate the premises; their assessment is in attempt
`05bc2722-960f-4ea4-bf1a-f92bb9a77af9`, not in any theorem.

`SustainingCausation` (#1493) located the existential-inertia dispute over the
immensity presence step (`8bf775e9`, IMMENSE_2 → IMMENSE_1) at one premise, the
sustaining reading of the tenseless cause of being (`23e04ae5`,
`CausingBeingIsSustaining`). Its attempt `c94eed5b` records that Feser's reply
needs an untyped premise: remaining in act (continuing to exist) needs an
actual actualizer at that time. This module types that premise and tests what
it derives.

**Concurrent actualization** (`ConcurrentActualization`, open). In every
history, whatever has its esse received in some principle (`EsseReceivedIn x z`,
DEF-ESSE-RECEIVED-IN: a principle standing to it as receiving potency to
received act) is, at every moment at which it is present, given being at that
moment by something (`GivesAt v g x t`, the #1493 primitive). The antecedent is
the act/potency notion "not its own being": its act of being is received in a
potency. The adopted `InPotency x esse` is not used, because DEF-POTENCY makes
potency exclude act in the same respect (CanBe ∧ ¬ InAct), so "present, hence in
act as to being, and in potency as to being" would be empty under
presence-in-act (`140544c4`). The *strong* version (`ConcurrentlyActualizedByAnother`)
requires the giver to be distinct from the thing: the form of Feser's reply,
which excludes the thing's own persistence power as the factor ("if the
additional factor is some other part of the water itself, then we will be back
with the circularity problem"). The derivation uses only the weak version.

*Meaning.* Remaining in received act at a moment is itself an actualization at
that moment, and an actualization needs an actual actualizer then. It combines
two theses that the text keeps apart: the actualization principle (a potency is
brought to act only by something in act) and the claim that *continuing* in
received act is, at each moment, a potency being actualized. Schmid grants a
principle close to the first for change (his (iii): a change occurs only if
some factor causally induces it) and denies the second (persistence is no
change). The typed premise does not split them: a primitive "actualized at t"
would be an opaque atom that nothing constrains.

*Examples.* The illumination of the air, which has no root in the air and lasts
only while the sun acts (ST I q.104 a.1 co., read; claims `40aefb2e`,
`da9c82ed`); a stone held aloft (a model of the time profile only: the stone's
being held, not its being, is given). *Counterexamples the inertialist offers*:
the persisting rock, the water in the glass (Feser's own example, Schmid's S):
on the inertialist account each persists through its earlier existence and the
absence of any factor inducing its cessation, with nothing giving it being at
the later moment. That is the rival account, not an established case: no case is
on file in which a received-esse thing is shown to persist with no giver.

*Structural properties.* A per-moment requirement: for each moment some giver
(`∀ t, ∃ g`). It does not require one giver at every moment (`∃ g, ∀ t`; the
relay interpretation of `Control` satisfies the strong version with different
givers at different moments), does not require the giver to be a cause of
being in the tenseless sense (`CausesIn`), and is silent on things whose esse is
not received.

**Concurrence of causes of being** (`CausesOfBeingConcur`, open). In every
history, whatever causes the being of another thing (`CausesIn c x esse`,
`c ≠ x`) gives it being at every moment at which anything gives it being. It
supplies the quantifier swap and the identification the derivation needs: from
"some giver at t" to "this cause gives at t". It is the per se ordering of givers
of being (a cause of the being of x acts on x whenever any giver of x's being
does), after the first cause's concurrence in every action (q.105 a.5, unread
here). The inertialist interpretation satisfies it (it constrains only moments
at which something gives).

**Weak sustaining reading** (`CausingAnothersBeingIsSustaining`). The
sustaining reading `23e04ae5` restricted to causes distinct from their effect.
It is all that the immensity presence step uses (the creator conjunct of
IMMENSE_2 is about every *other* being), and it is entailed by `23e04ae5`
(`Control` part 5 shows the converse fails for a self-cause).

Applicability of every premise below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.ConcurrentActualization

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Causality.DeiFiliusImmenseIncomprehensible (IsImmenseAsInfiniteCauseOfAll)

/-- Concurrent actualization, weak version: in every history, whatever has its
esse received in some principle is, at every moment at which it is present,
given being at that moment by something. -/
def ConcurrentlyActualized {W B T P : Type} (h : History W B T) (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x t z, EsseReceivedIn x z → h.IsAt v x t → ∃ g, G.GivesAt v g x t

/-- Concurrent actualization, strong version: the giver at each moment is
distinct from the thing. Excludes a thing's own persistence power as the
factor. -/
def ConcurrentlyActualizedByAnother {W B T P : Type} (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x t z, EsseReceivedIn x z → h.IsAt v x t → ∃ g, g ≠ x ∧ G.GivesAt v g x t

/-- Concurrence of causes of being: in every history, whatever causes the being
of another thing gives it being at every moment at which anything gives it
being. -/
def CausesOfBeingConcur {W B T Respect : Type} (G : BeingGiving W B T)
    (CausesIn : B → B → Respect → Prop) (esse : Respect) : Prop :=
  ∀ v c g x t, c ≠ x → CausesIn c x esse → G.GivesAt v g x t → G.GivesAt v c x t

/-- Weak sustaining reading: in every history, a cause of the being of another
thing that is present at some moment is a CAUSE_OF_BEING_2 sustaining cause of
it. -/
def CausingAnothersBeingIsSustaining {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect) : Prop :=
  ∀ v c x, c ≠ x → CausesIn c x esse → (∃ t, h.IsAt v x t) → SustainsBeing h G v c x

namespace Control

open TruthCore.Causality.SustainingCausation.Control

/-- `false` alone has received esse. -/
def falseReceived : Bool → Unit → Prop := fun x _ => x = false

/-- Nothing has received esse. -/
def noneReceived : Bool → Unit → Prop := fun _ _ => False

/-- Intrinsic persistence power: `true` gives `false` being at time `1`, and
`false` gives itself being at every time from `1` on. -/
def selfGiving : BeingGiving Unit Bool Nat :=
  ⟨fun _ c x t => x = false ∧ ((c = true ∧ t = 1) ∨ (c = false ∧ 1 ≤ t))⟩

/-- Every thing causes its own being, and nothing causes another's. -/
def selfCauses : Bool → Bool → Unit → Prop := fun c x _ => c = x

/-- Relay: `0` (the original cause) is present at times `0` and `1`, `1` (the
effect) from time `1` on, `2` (a later sustainer) at every time. -/
def relay : History Unit (Fin 3) Nat where
  ontic := { frame := unitFrame, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  IsAt := fun _ b t => (b = 0 ∧ t ≤ 1) ∨ (b = 1 ∧ 1 ≤ t) ∨ b = 2
  now := 1

/-- `0` gives `1` being at time `1`; `2` gives `1` being at every time from `2` on. -/
def relayGiving : BeingGiving Unit (Fin 3) Nat :=
  ⟨fun _ c x t => x = 1 ∧ ((c = 0 ∧ t = 1) ∨ (c = 2 ∧ 2 ≤ t))⟩

/-- `0` causes the being of `1`. -/
def relayCauses : Fin 3 → Fin 3 → Unit → Prop := fun c x _ => c = 0 ∧ x = 1

/-- `1` alone has received esse. -/
def oneReceived : Fin 3 → Unit → Prop := fun x _ => x = 1

/-- Rival-reading, omission, strictness and nonvacuity controls, every
interpretation with one world and natural-number times; the Bool histories are
those of `SustainingCausation.Control`.
(1) Extrinsic existential inertia (`inertia`; Schmid's no-change account):
`true` gives `false` being at time `1` only; `false` persists from time `1` on.
The reception bridge, concurrence, presence-in-act and contact hold; concurrent
actualization fails (weak version), the weak sustaining reading fails, and the
IMMENSE_2 being is not present to all whenever they are.
(2) Intrinsic persistence power (`inertia` with `selfGiving`): the reception
bridge, the weak concurrent actualization and contact hold; the strong version,
concurrence and the weak sustaining reading fail.
(3) Relay (`relay`): a later sustainer `2` replaces the original cause `0`. The
reception bridge, the strong concurrent actualization and contact hold;
concurrence and the weak sustaining reading fail.
(4) No received esse (`inertia`): concurrent actualization (both versions) and
concurrence hold; the reception bridge and the weak sustaining reading fail.
(5) Self-causes (`sustained`, no giving): the weak sustaining reading holds and
the sustaining reading `23e04ae5` fails.
(6) `absentGiver` with giving at every time: the weak sustaining reading and
presence-in-act hold, contact and presence to all fail. `sustained` with nothing
in act and no causes: the weak sustaining reading and contact hold,
presence-in-act and presence to all fail.
(7) `sustained` with its giving: every premise (both versions of concurrent
actualization), both sustaining readings and presence to all hold, and `true`
is IMMENSE_2. -/
def Certificate : Prop :=
  (CausedEsseIsReceived trueCausesFalse () falseReceived ∧
    CausesOfBeingConcur inertiaGiving trueCausesFalse () ∧
    PresentIsInActAsToBeing inertia everything () ∧
    GiverPresentWhenGiving inertia inertiaGiving ∧
    ¬ ConcurrentlyActualized inertia inertiaGiving falseReceived ∧
    ¬ CausingAnothersBeingIsSustaining inertia inertiaGiving trueCausesFalse () ∧
    IsImmenseAsInfiniteCauseOfAll everything trueCausesFalse () isTrue true ∧
    ¬ Immense2PresentToAll inertia inertiaGiving everything trueCausesFalse () isTrue) ∧
  (CausedEsseIsReceived trueCausesFalse () falseReceived ∧
    ConcurrentlyActualized inertia selfGiving falseReceived ∧
    GiverPresentWhenGiving inertia selfGiving ∧
    ¬ ConcurrentlyActualizedByAnother inertia selfGiving falseReceived ∧
    ¬ CausesOfBeingConcur selfGiving trueCausesFalse () ∧
    ¬ CausingAnothersBeingIsSustaining inertia selfGiving trueCausesFalse ()) ∧
  (CausedEsseIsReceived relayCauses () oneReceived ∧
    ConcurrentlyActualizedByAnother relay relayGiving oneReceived ∧
    GiverPresentWhenGiving relay relayGiving ∧
    ¬ CausesOfBeingConcur relayGiving relayCauses () ∧
    ¬ CausingAnothersBeingIsSustaining relay relayGiving relayCauses ()) ∧
  (¬ CausedEsseIsReceived trueCausesFalse () noneReceived ∧
    ConcurrentlyActualizedByAnother inertia inertiaGiving noneReceived ∧
    ConcurrentlyActualized inertia inertiaGiving noneReceived ∧
    CausesOfBeingConcur inertiaGiving trueCausesFalse () ∧
    ¬ CausingAnothersBeingIsSustaining inertia inertiaGiving trueCausesFalse ()) ∧
  (CausingAnothersBeingIsSustaining sustained noGiving selfCauses () ∧
    ¬ CausingBeingIsSustaining sustained noGiving selfCauses ()) ∧
  (CausingAnothersBeingIsSustaining absentGiver alwaysGiving trueCausesFalse () ∧
    PresentIsInActAsToBeing absentGiver everything () ∧
    ¬ GiverPresentWhenGiving absentGiver alwaysGiving ∧
    ¬ Immense2PresentToAll absentGiver alwaysGiving everything trueCausesFalse () isTrue ∧
    CausingAnothersBeingIsSustaining sustained noGiving noCauses () ∧
    GiverPresentWhenGiving sustained noGiving ∧
    ¬ PresentIsInActAsToBeing sustained nothing () ∧
    ¬ Immense2PresentToAll sustained noGiving nothing noCauses () isTrue) ∧
  (CausedEsseIsReceived trueCausesFalse () falseReceived ∧
    ConcurrentlyActualizedByAnother sustained sustainedGiving falseReceived ∧
    ConcurrentlyActualized sustained sustainedGiving falseReceived ∧
    CausesOfBeingConcur sustainedGiving trueCausesFalse () ∧
    CausingAnothersBeingIsSustaining sustained sustainedGiving trueCausesFalse () ∧
    CausingBeingIsSustaining sustained sustainedGiving trueCausesFalse () ∧
    PresentIsInActAsToBeing sustained everything () ∧
    GiverPresentWhenGiving sustained sustainedGiving ∧
    IsImmenseAsInfiniteCauseOfAll everything trueCausesFalse () isTrue true ∧
    Immense2PresentToAll sustained sustainedGiving everything trueCausesFalse () isTrue)

end Control

end TruthCore.Causality.ConcurrentActualization
