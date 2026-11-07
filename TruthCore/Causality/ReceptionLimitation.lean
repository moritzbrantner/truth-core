module

public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Causality.EsseReceptionDefinitionFork
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-! Limitation through reception: deriving the #320 whole-power bridges from
ST I q.7 a.1–2 and q.4 a.1 ad 3

Analyst formulations, attribution deferred. Each premise below is a reading of a
sentence in a pinned passage, recorded as a `supports` relation from an existing
claim with its gap; none is attributed as stated.

ST I q.7 a.1 co. explains limitation by reception: a form "per hoc quod
recipitur in materia, fit forma determinate huius rei", matter contracts its
amplitude, and since esse is "maxime formale omnium", God, whose esse "non sit
esse receptum in aliquo, sed ipse sit suum esse subsistens", is infinite. Ad 3
joins "per se subsistens" and "non receptum in aliquo" in God's esse, and says a
subsistent whiteness, by not being in another, would differ from all whiteness
in a subject; it never infers subsistence from non-reception. Q.7 a.2 co. says the esse of a
subsistent created form, which "non est suum esse", is "receptum et contractum".
Q.4 a.1 ad 3 says esse "non comparatur ad alia sicut recipiens ad receptum".

Vocabulary reused: `EsseReceivedIn` (DEF-ESSE-RECEIVED-IN), `EsseLimited`
(DEF-ESSE-LIMITED), the primitive `Infinite` (DEF-INFINITE), `OwnBeing` (SCG I.28,
own subsistent being), `Has`/`Pure`/`OfBeing` of `WholePowerPerfection`. The one
new primitive is `Recipient x` (DEF-RECIPIENT): some act is received in x, so x
contains a principle standing to an act as receiving potency (matter to form, a
created essence to its esse, a subject to its accidents). It is not
`EsseReceivedIn` (reception of x's esse in a given principle; nothing here says a
being with received esse is a `Recipient`) and not the legacy `InPotency x r`
(able to have a respect without having it). Examples: a piece of wood (its matter
receives its form, it is in potency to further shapes, q.7 a.2 co.); counterexample:
subsistent esse as q.4 a.1 ad 3 describes it.

The derivations replace no source claim and edit no existing statement. -/

@[expose] public section

namespace TruthCore.Causality.ReceptionLimitation

variable {B P D : Type}

/-- q.7 a.1 co. with ad 3, read as a general conditional: whatever has an esse
received in no principle is its own subsistent being. The source asserts both
halves of God, and ad 3 joins them in God's esse; the general conditional, from
non-reception to subsistence, is the analyst's reading. It is only as strong as the reception
relation is complete: if an interpretation records no reception at all, every
being is its own being. -/
def UnreceivedEsseIsOwnBeing (EsseReceivedIn : B → P → Prop) (OwnBeing : B → Prop) : Prop :=
  ∀ x, (∀ r, ¬ EsseReceivedIn x r) → OwnBeing x

/-- q.4 a.1 ad 3, read for subsistent esse: what is its own being is no
recipient. Esse "non comparatur ad alia sicut recipiens ad receptum"; the step
to "a being that is its own esse receives no act" is the analyst's. -/
def OwnBeingIsNoRecipient (OwnBeing Recipient : B → Prop) : Prop :=
  ∀ x, OwnBeing x → ¬ Recipient x

/-- q.7 a.1 co., generalized from form and esse to every real determination: a
being in which nothing is received has only pure determinations. A form is
determined and contracted by the matter that receives it, and "infinitum
secundum quod se tenet ex parte formae non determinatae per materiam, habet
rationem perfecti". That reception is the only source of limitation, the
generalization, and the claim
that individuating principles, potencies and privations (the other non-pure
determinations of DEF-PURE-PERFECTION) occur only in recipients, are the
analyst's. -/
def NonRecipientDeterminationsArePure (Recipient : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) : Prop :=
  ∀ x, ¬ Recipient x → ∀ d, Has x d → Pure d

/-- q.7 a.1 co., the other half of "infinitum dicitur aliquid ex eo quod non est
finitum": whatever is infinite (infinity of perfection, simpliciter) does not
have limited esse. Q.7 a.2 calls subsistent created forms and prime matter
infinite only secundum quid; they are not `Infinite` in this sense. -/
def InfiniteEsseIsUnlimited (EsseLimited Infinite : B → Prop) : Prop :=
  ∀ x, Infinite x → ¬ EsseLimited x

/-- q.7 a.2 co.: received esse is contracted, hence limited. The source says it
of a subsistent created form ("ipsum eius esse sit receptum et contractum ad
determinatam naturam"); the generalization to every received esse is the
analyst's. Converse of `EsseLimitedOnlyThroughReceptionReading`. -/
def ReceivedEsseIsLimited (EsseLimited : B → Prop) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ x r, EsseReceivedIn x r → EsseLimited x

/-- q.7 a.1 co., with own being as the primitive: whatever is its own subsistent
being is infinite. The existing reading `SubsistentBeingIsInfiniteReading` uses a
represented essence/esse equality instead; this one uses `OwnBeing`. -/
def OwnBeingIsInfinite (OwnBeing Infinite : B → Prop) : Prop :=
  ∀ x, OwnBeing x → Infinite x

namespace Control
open TruthCore.Causality.EsseReceptionDefinitionFork (Frame)

/-- One being, two principles; the being's represented essence and esse are both
`false`, and `Rec r` says its esse is received in `r`. -/
def frame (Rec : Bool → Prop) : Frame where
  Being := Unit
  Principle := Bool
  State := Unit
  selected := ()
  human := ()
  soulOf := fun _ => ()
  bodyOf := fun _ => false
  essenceOf := fun _ => false
  esseOf := fun _ => false
  communicatedAct := false
  Unites := fun _ _ _ _ => False
  Communicates := fun _ _ _ _ => False
  Received := fun _ _ r => Rec r
  Eligible := fun _ _ => False

/-- No reception. -/
def noRec : Frame := frame (fun _ => False)
/-- Esse received in the being's own essence `false`. -/
def ownRec : Frame := frame (fun r => r = false)
/-- Esse received in the other principle `true`. -/
def otherRec : Frame := frame (fun r => r = true)

def potNone (_ _ : Bool) : Prop := False
def potAll (_ _ : Bool) : Prop := True
/-- `true` is in receptive potency to `false`, and nothing else. -/
def potTrue (p a : Bool) : Prop := p = true ∧ a = false

def no1 (_ : Unit) : Prop := False
def no2 (_ _ : Unit) : Prop := False
def yes1 (_ : Unit) : Prop := True
def no11 (_ : Unit) (_ : Unit) : Prop := False
def yes11 (_ : Unit) (_ : Unit) : Prop := True
def noD (_ : Unit) : Prop := False
def yesD (_ : Unit) : Prop := True

/-- The four inputs of the own-being derivation on a frame. -/
def OwnInputs (f : Frame) (pot : f.Principle → f.Principle → Prop)
    (Own : f.Being → Prop) : Prop :=
  TruthCore.Causality.EsseReceptionDefinitionFork.IdentityScopedOwnEssence f ∧
  TruthCore.Latin.Aquinas.DeEnte.ReceiverInPotencyToReceivedEsseReading f.esseOf
    (f.Received f.selected) pot ∧
  TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself pot ∧
  UnreceivedEsseIsOwnBeing (f.Received f.selected) Own

open TruthCore.Causality.EsseReceptionDefinitionFork (IdentityScopedOwnEssence)
open TruthCore.Latin.Aquinas.DeEnte (ReceiverInPotencyToReceivedEsseReading)
open TruthCore.Causality.EsseReception (NothingInReceptivePotencyToItself)
open TruthCore.Causality.WholePowerPerfection
open TruthCore.Causality.RootPurity (UnlimitedDeterminationsArePure)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception
  (UnlimitedEsseIsInfiniteReading)

/-- Finite interpretations; one omission control per premise of each derivation
and a positive witness for each. Every frame has one being whose represented
esse equals its represented essence, which is not composite and has nothing
prior, so it has no represented limiting principle.
* Own being, omitting the q.7 a.1 reading: nothing is received, the being is not
  its own being. Omitting irreflexivity: esse is received in its own essence,
  which is in potency to itself. Omitting the De ente reading: esse is received
  in its own essence, which is in potency to nothing. Omitting the
  identity-scoped own-essence premise: esse is received in the other principle.
  In each, the own-being bridge fails, and with a recipient that has a non-pure
  determination the purity bridge fails while q.4 a.1 ad 3 and the q.7 a.1
  generalization hold.
* Purity, omitting q.4 a.1 ad 3: the being is its own being and a recipient.
  Omitting the q.7 a.1 generalization: it is its own being, no recipient, and
  has a non-pure determination.
* Infinite perfection (the being is infinite and lacks the one pure
  perfection), omitting in turn the converse definition of infinity, q.7 a.2,
  the q.7 a.1 reading, SCG I.28, and q.4 a.2.
* Unlimited esse is infinite (the being's esse is unlimited and it is not
  infinite), omitting in turn q.7 a.2, the q.7 a.1 reading, and own being is
  infinite. -/
def Certificate : Prop :=
  -- own being and purity: omit the q.7 a.1 reading
  (IdentityScopedOwnEssence noRec ∧
    ReceiverInPotencyToReceivedEsseReading noRec.esseOf (noRec.Received noRec.selected) potNone ∧
    NothingInReceptivePotencyToItself potNone ∧
    ¬ UnreceivedEsseIsOwnBeing (noRec.Received noRec.selected) no1 ∧
    ¬ UnlimitedIsOwnBeing no1 no2 noRec.essenceOf noRec.esseOf no1 ∧
    OwnBeingIsNoRecipient no1 yes1 ∧ NonRecipientDeterminationsArePure yes1 yes11 noD ∧
    ¬ UnlimitedDeterminationsArePure no1 no2 noRec.essenceOf noRec.esseOf yes11 noD) ∧
  -- omit irreflexivity
  (IdentityScopedOwnEssence ownRec ∧
    ReceiverInPotencyToReceivedEsseReading ownRec.esseOf (ownRec.Received ownRec.selected) potAll ∧
    ¬ NothingInReceptivePotencyToItself potAll ∧
    UnreceivedEsseIsOwnBeing (ownRec.Received ownRec.selected) no1 ∧
    ¬ UnlimitedIsOwnBeing no1 no2 ownRec.essenceOf ownRec.esseOf no1 ∧
    OwnBeingIsNoRecipient no1 yes1 ∧ NonRecipientDeterminationsArePure yes1 yes11 noD ∧
    ¬ UnlimitedDeterminationsArePure no1 no2 ownRec.essenceOf ownRec.esseOf yes11 noD) ∧
  -- omit the De ente receiver-in-potency reading
  (IdentityScopedOwnEssence ownRec ∧
    ¬ ReceiverInPotencyToReceivedEsseReading ownRec.esseOf (ownRec.Received ownRec.selected) potNone ∧
    NothingInReceptivePotencyToItself potNone ∧
    UnreceivedEsseIsOwnBeing (ownRec.Received ownRec.selected) no1 ∧
    ¬ UnlimitedIsOwnBeing no1 no2 ownRec.essenceOf ownRec.esseOf no1 ∧
    OwnBeingIsNoRecipient no1 yes1 ∧ NonRecipientDeterminationsArePure yes1 yes11 noD ∧
    ¬ UnlimitedDeterminationsArePure no1 no2 ownRec.essenceOf ownRec.esseOf yes11 noD) ∧
  -- omit identity-scoped own essence
  (¬ IdentityScopedOwnEssence otherRec ∧
    ReceiverInPotencyToReceivedEsseReading otherRec.esseOf (otherRec.Received otherRec.selected) potTrue ∧
    NothingInReceptivePotencyToItself potTrue ∧
    UnreceivedEsseIsOwnBeing (otherRec.Received otherRec.selected) no1 ∧
    ¬ UnlimitedIsOwnBeing no1 no2 otherRec.essenceOf otherRec.esseOf no1 ∧
    OwnBeingIsNoRecipient no1 yes1 ∧ NonRecipientDeterminationsArePure yes1 yes11 noD ∧
    ¬ UnlimitedDeterminationsArePure no1 no2 otherRec.essenceOf otherRec.esseOf yes11 noD) ∧
  -- own-being positive witness
  (OwnInputs noRec potNone yes1 ∧ UnlimitedIsOwnBeing no1 no2 noRec.essenceOf noRec.esseOf yes1) ∧
  -- purity: omit q.4 a.1 ad 3
  (OwnInputs noRec potNone yes1 ∧ ¬ OwnBeingIsNoRecipient yes1 yes1 ∧
    NonRecipientDeterminationsArePure yes1 yes11 noD ∧
    ¬ UnlimitedDeterminationsArePure no1 no2 noRec.essenceOf noRec.esseOf yes11 noD) ∧
  -- purity: omit the q.7 a.1 generalization
  (OwnInputs noRec potNone yes1 ∧ OwnBeingIsNoRecipient yes1 no1 ∧
    ¬ NonRecipientDeterminationsArePure no1 yes11 noD ∧
    ¬ UnlimitedDeterminationsArePure no1 no2 noRec.essenceOf noRec.esseOf yes11 noD) ∧
  -- purity positive witness
  (OwnInputs noRec potNone yes1 ∧ OwnBeingIsNoRecipient yes1 no1 ∧
    NonRecipientDeterminationsArePure no1 yes11 yesD ∧
    UnlimitedDeterminationsArePure no1 no2 noRec.essenceOf noRec.esseOf yes11 yesD) ∧
  -- infinite perfection: omit the converse definition of infinity
  (¬ InfiniteEsseIsUnlimited yes1 yes1 ∧ ReceivedEsseIsLimited yes1 yes11 ∧
    UnreceivedEsseIsOwnBeing yes11 no1 ∧ OwnBeingLacksNoPerfectionOfBeing no1 no11 yesD ∧
    PurePerfectionsPertainToBeing yesD yesD ∧ ¬ InfiniteHasEveryPurePerfection yes1 no11 yesD) ∧
  -- omit q.7 a.2
  (InfiniteEsseIsUnlimited no1 yes1 ∧ ¬ ReceivedEsseIsLimited no1 yes11 ∧
    UnreceivedEsseIsOwnBeing yes11 no1 ∧ OwnBeingLacksNoPerfectionOfBeing no1 no11 yesD ∧
    PurePerfectionsPertainToBeing yesD yesD ∧ ¬ InfiniteHasEveryPurePerfection yes1 no11 yesD) ∧
  -- omit the q.7 a.1 reading
  (InfiniteEsseIsUnlimited no1 yes1 ∧ ReceivedEsseIsLimited no1 no11 ∧
    ¬ UnreceivedEsseIsOwnBeing no11 no1 ∧ OwnBeingLacksNoPerfectionOfBeing no1 no11 yesD ∧
    PurePerfectionsPertainToBeing yesD yesD ∧ ¬ InfiniteHasEveryPurePerfection yes1 no11 yesD) ∧
  -- omit SCG I.28
  (InfiniteEsseIsUnlimited no1 yes1 ∧ ReceivedEsseIsLimited no1 no11 ∧
    UnreceivedEsseIsOwnBeing no11 yes1 ∧ ¬ OwnBeingLacksNoPerfectionOfBeing yes1 no11 yesD ∧
    PurePerfectionsPertainToBeing yesD yesD ∧ ¬ InfiniteHasEveryPurePerfection yes1 no11 yesD) ∧
  -- omit q.4 a.2
  (InfiniteEsseIsUnlimited no1 yes1 ∧ ReceivedEsseIsLimited no1 no11 ∧
    UnreceivedEsseIsOwnBeing no11 yes1 ∧ OwnBeingLacksNoPerfectionOfBeing yes1 no11 noD ∧
    ¬ PurePerfectionsPertainToBeing yesD noD ∧ ¬ InfiniteHasEveryPurePerfection yes1 no11 yesD) ∧
  -- infinite perfection positive witness
  (InfiniteEsseIsUnlimited no1 yes1 ∧ ReceivedEsseIsLimited no1 no11 ∧
    UnreceivedEsseIsOwnBeing no11 yes1 ∧ OwnBeingLacksNoPerfectionOfBeing yes1 yes11 yesD ∧
    PurePerfectionsPertainToBeing yesD yesD ∧ InfiniteHasEveryPurePerfection yes1 yes11 yesD) ∧
  -- unlimited esse is infinite: omit q.7 a.2
  (¬ ReceivedEsseIsLimited no1 yes11 ∧ UnreceivedEsseIsOwnBeing yes11 no1 ∧
    OwnBeingIsInfinite no1 no1 ∧ ¬ UnlimitedEsseIsInfiniteReading no1 no1) ∧
  -- omit the q.7 a.1 reading
  (ReceivedEsseIsLimited no1 no11 ∧ ¬ UnreceivedEsseIsOwnBeing no11 no1 ∧
    OwnBeingIsInfinite no1 no1 ∧ ¬ UnlimitedEsseIsInfiniteReading no1 no1) ∧
  -- omit own being is infinite
  (ReceivedEsseIsLimited no1 no11 ∧ UnreceivedEsseIsOwnBeing no11 yes1 ∧
    ¬ OwnBeingIsInfinite yes1 no1 ∧ ¬ UnlimitedEsseIsInfiniteReading no1 no1) ∧
  -- positive witness
  (ReceivedEsseIsLimited no1 no11 ∧ UnreceivedEsseIsOwnBeing no11 yes1 ∧
    OwnBeingIsInfinite yes1 yes1 ∧ UnlimitedEsseIsInfiniteReading no1 yes1)

end Control
end TruthCore.Causality.ReceptionLimitation
