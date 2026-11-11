module

@[expose] public section
namespace TruthCore.Logic.RecognitionTranscript

/-- A tiny stipulated language: the message instructs the addressed recipient
on the stated occasion to echo the challenge token. Tokens are identifiers,
not secrets by type. No author is contained in this public syntax. -/
structure Message where
  recipient : Nat
  occasion : Nat
  token : Nat
  deriving DecidableEq

/-- Parsing/response convention: the reply echoes all three public fields.
This fixes symbolic content, not a person's comprehension or intention. -/
def Responds (challenge reply : Message) : Prop := reply = challenge

/-- Independently supplied production history. Access lists tokens available
before production; originTime records production time. Delivery time and its
ordering are not encoded. These are actual stipulated history fields, not a
public report that the fields have these values. -/
structure History where
  visible : Message
  origin : Nat
  originTime : Nat
  originToken : Nat
  access : Nat → List Nat

/-- Integrity binds the displayed token to the production token. Freshness
forbids that token in earlier productions. Access discipline forbids producing
a token absent from the producer's prior access. None follows from syntax. -/
def Integrity (h : History) : Prop := h.visible.token = h.originToken
def Fresh (challenge : Message) (h : History) : Prop :=
  h.originTime < challenge.occasion → h.originToken ≠ challenge.token
def Disciplined (h : History) : Prop := h.originToken ∈ h.access h.origin
def Exclusive (g : Nat) (challenge : Message) (h : History) : Prop :=
  ∀ p, challenge.token ∈ h.access p → p = g

/-- Actual production of the response token by g on or after the challenge occasion, rather than a
copied older production by g. Whole-message authorship, address authorization, delivery agency and divine identity are absent. -/
def AuthoredNow (g : Nat) (challenge : Message) (h : History) : Prop :=
  h.origin = g ∧ ¬ h.originTime < challenge.occasion

/-- Universal conditional with the same fixed challenge and candidate.
Freshness excludes old production; actual exclusive access excludes a
contemporary ordinary producer, conditional on integrity/access discipline. -/
def Attribution : Prop := ∀ (g : Nat) (c : Message) (h : History),
  Responds c h.visible → Integrity h → Fresh c h → Disciplined h →
  Exclusive g c h → AuthoredNow g c h

abbrev challenge : Message := ⟨7, 10, 42⟩
abbrev genuine : History := ⟨challenge, 0, 10, 42, fun p => if p = 0 then [42] else []⟩
abbrev forgery : History := ⟨challenge, 1, 10, 42, fun _ => [42]⟩
abbrev replay : History := ⟨challenge, 0, 9, 42, genuine.access⟩
abbrev insertion : History := ⟨challenge, 1, 10, 11, fun p => if p = 0 then [42] else [11]⟩
abbrev guess : History := ⟨challenge, 1, 10, 42, genuine.access⟩

/-- Inhabited positive bundle and four distinct omissions, preserving exactly
one visible transcript, candidate, task, occasion and recipient. The guess
omits deterministic access discipline, which ordinary guessing can violate. -/
def Controls : Prop :=
  (Responds challenge genuine.visible ∧ Integrity genuine ∧ Fresh challenge genuine ∧
    Disciplined genuine ∧ Exclusive 0 challenge genuine ∧ AuthoredNow 0 challenge genuine) ∧
  (forgery.visible = genuine.visible ∧ Integrity forgery ∧ Fresh challenge forgery ∧
    Disciplined forgery ∧ ¬ Exclusive 0 challenge forgery ∧ ¬ AuthoredNow 0 challenge forgery) ∧
  (replay.visible = genuine.visible ∧ Integrity replay ∧ Disciplined replay ∧
    Exclusive 0 challenge replay ∧ ¬ Fresh challenge replay ∧ ¬ AuthoredNow 0 challenge replay) ∧
  (insertion.visible = genuine.visible ∧ Fresh challenge insertion ∧ Disciplined insertion ∧
    Exclusive 0 challenge insertion ∧ ¬ Integrity insertion ∧ ¬ AuthoredNow 0 challenge insertion) ∧
  (guess.visible = genuine.visible ∧ Integrity guess ∧ Fresh challenge guess ∧
    Exclusive 0 challenge guess ∧ ¬ Disciplined guess ∧ ¬ AuthoredNow 0 challenge guess)

end TruthCore.Logic.RecognitionTranscript
