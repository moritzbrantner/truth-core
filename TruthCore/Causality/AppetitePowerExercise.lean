module

/-! Semantic interface for actual willing episodes (ST I q.19 a.1–2).
The subject, object and occasion domains are arbitrary; an occasion need not be
an instant or a temporal change. Relations below are explicitly primitive:
recognizing love, delight and communication in a concrete interpretation is an
open semantic obligation, not something a response name proves. This interface
does not identify a soul's passive power with divine willing or with HasWill. -/
@[expose] public section
namespace TruthCore.Causality.AppetitePowerExercise

/-- Independently interpreted episode relations. Apprehension is aspect-relative:
an object can be apprehended as suitable without being objectively good.
Possession concerns this good for this subject, not exclusive ownership.
Seeking is directed toward obtaining it; love affirms a possessed good; delight
rests in it. Communication shares a possessed good with a recipient and need
not deprive its giver. Possibility is not actuality or guaranteed production.
No causal, temporal, maximizing or passive-faculty laws are built in. -/
structure Interpretation where
  Subject : Type
  Object : Type
  Occasion : Type
  isSoul : Subject → Prop
  apprehendsSuitable : Subject → Object → Occasion → Prop
  apprehendsGood : Subject → Object → Occasion → Prop
  possessed : Subject → Object → Occasion → Prop
  seeks : Subject → Object → Occasion → Prop
  loves : Subject → Object → Occasion → Prop
  delights : Subject → Object → Occasion → Prop
  canCommunicate : Subject → Subject → Object → Occasion → Prop
  communicates : Subject → Subject → Object → Occasion → Prop

/-- Possible appetitive modes; these tags alone assert neither ability nor act. -/
inductive Response (Subject : Type) where
  | seek | love | delight
  | communicate (recipient : Subject)

/-- Relational content of a soul-relative power. `possible` means an appetitive
ability, not mere locomotor ability or a relation fixed only by natural form.
It is primitive; its application must be interpreted independently of cognition.
The laws make the object follow suitable/good apprehension and distinguish
absence, possession and possible sharing. They impose no total responsiveness.
An empty content is allowed as a specification, but does not meet `Possessed`.
No numerical ranking, maximization, or actual willing is demanded. -/
structure Capacity (m : Interpretation) (s : m.Subject) where
  possible : m.Object → m.Occasion → Response m.Subject → Prop
  apprehension : ∀ o t r, possible o t r →
    m.apprehendsSuitable s o t ∨ m.apprehendsGood s o t
  seeking : ∀ o t, possible o t .seek → ¬ m.possessed s o t
  loving : ∀ o t, possible o t .love → m.possessed s o t
  delighting : ∀ o t, possible o t .delight → m.possessed s o t
  communicating : ∀ o t recipient, possible o t (.communicate recipient) →
    m.possessed s o t ∧ m.canCommunicate s recipient o t

/-- An admission condition for a bearer, separately from the specification of
relational content: a soul with a nonempty appetitive ability. The witness may
be at any occasion; it asserts no current act and no response to every good.
Realizing this possible-response relation as a soul's power remains an explicit
interpretation obligation, as does recognition by the existing HasWill. -/
def Capacity.Possessed {m : Interpretation} {s : m.Subject}
    (c : Capacity m s) : Prop :=
  m.isSoul s ∧ ∃ o t r, c.possible o t r

/-- Actual exercise is evidence of a suitably situated act, not an available
response, chosen policy or mere action tag. The constructors preserve absent
and possessed cases and require possible communication when it occurs.
No implication from an intellectual-power label to an inhabitant is asserted. -/
inductive Exercise (m : Interpretation) (s : m.Subject) (o : m.Object)
    (t : m.Occasion) : Type where
  | seeking : m.apprehendsGood s o t → ¬ m.possessed s o t →
      m.seeks s o t → Exercise m s o t
  | loving : m.apprehendsGood s o t → m.possessed s o t →
      m.loves s o t → Exercise m s o t
  | delighting : m.apprehendsGood s o t → m.possessed s o t →
      m.delights s o t → Exercise m s o t
  | communicating (recipient : m.Subject) :
      m.apprehendsGood s o t → m.possessed s o t →
      m.canCommunicate s recipient o t → m.communicates s recipient o t →
      Exercise m s o t

/-- Populated apprehension of possessed good with love but no seeking,
delight or communication. A semantic control, not a divine model. -/
def possessedLove : Interpretation where
  Subject := Unit
  Object := Unit
  Occasion := Unit
  isSoul := fun _ => True
  apprehendsSuitable := fun _ _ _ => True
  apprehendsGood := fun _ _ _ => True
  possessed := fun _ _ _ => True
  seeks := fun _ _ _ => False
  loves := fun _ _ _ => True
  delights := fun _ _ _ => False
  canCommunicate := fun _ _ _ _ => True
  communicates := fun _ _ _ _ => False

/-- Same populated apprehension and communication possibility, no actual act. -/
def idle : Interpretation :=
  { possessedLove with loves := fun _ _ _ => False }

/-- Love is possible at the populated represented good, with no present act. -/
def idleCapacity : Capacity idle () where
  possible := fun _ _ r => r = .love
  apprehension := fun _ _ _ _ => Or.inl True.intro
  seeking := fun _ _ h => nomatch h
  loving := fun _ _ _ => True.intro
  delighting := fun _ _ h => nomatch h
  communicating := fun _ _ _ h => nomatch h

/-- Purely cognitive interpretation with the same appraisal but no appetitive
ability. Its empty specification fails possession of a nonempty capacity. -/
def cognitiveOnly : Capacity idle () where
  possible := fun _ _ _ => False
  apprehension := fun _ _ _ h => False.elim h
  seeking := fun _ _ h => False.elim h
  loving := fun _ _ h => False.elim h
  delighting := fun _ _ h => False.elim h
  communicating := fun _ _ _ h => False.elim h

/-- Two equally apprehended possessed goods. Selectivity remains permitted. -/
def twoGoods : Interpretation where
  Subject := Unit
  Object := Bool
  Occasion := Unit
  isSoul := fun _ => True
  apprehendsSuitable := fun _ _ _ => True
  apprehendsGood := fun _ _ _ => True
  possessed := fun _ _ _ => True
  seeks := fun _ _ _ => False
  loves := fun _ _ _ => False
  delights := fun _ _ _ => False
  canCommunicate := fun _ _ _ _ => False
  communicates := fun _ _ _ _ => False

def selective : Capacity twoGoods () where
  possible := fun o _ r => o = false ∧ r = .love
  apprehension := fun _ _ _ _ => Or.inl True.intro
  seeking := fun _ _ h => nomatch h.2
  loving := fun _ _ _ => True.intro
  delighting := fun _ _ h => nomatch h.2
  communicating := fun _ _ _ h => nomatch h.2

example : selective.Possessed ∧
    twoGoods.apprehendsGood () true () ∧
    ¬ (∃ r, selective.possible true () r) := by
  refine ⟨⟨True.intro, false, (), .love, rfl, rfl⟩, True.intro, ?_⟩
  rintro ⟨_, h, _⟩
  contradiction

example : idleCapacity.Possessed :=
  ⟨True.intro, ⟨(), (), .love, rfl⟩⟩

example : ¬ cognitiveOnly.Possessed := by
  rintro ⟨_, o, t, r, h⟩
  exact h

example : Exercise possessedLove () () () :=
  .loving True.intro True.intro True.intro

example : Exercise idle () () () → False := by
  intro e
  cases e with
  | seeking _ _ act => exact act
  | loving _ _ act => exact act
  | delighting _ _ act => exact act
  | communicating _ _ _ _ act => exact act

end TruthCore.Causality.AppetitePowerExercise
