import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.105 a.5 co.
and ad 3 (*utrum Deus operetur in omni operante*).

Basis: the English Dominican translation (2nd rev. ed. 1920), pinned as the web
snapshot `AQUINAS-ST-I-Q105-A5-EN`; SCTA has no Latin text for this question.
The reading is a candidate for upgrade once a pinned Latin witness exists.

Vocabulary as in the *prima via* (`MovedIn`, `MovesIn`) and the *quarta via*
(`InAct`, `CausesIn`, `esse`, `CausesAllInGenus`).
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- The cause of the being of all things moves to act every agent whose being it
causes: "God not only moves things to operate, as it were applying their forms
and powers to operation ...; but He also gives created agents their forms and
preserves them in being" (co., third way); "God not only gives things their
form, but He also preserves them in existence, and applies them to act" (ad 3).

"God" is read through the description the article itself gives, "the First and
Universal Cause", "properly the cause of universal being which is innermost in
all things": a being that causes the being of every other being
(`CausesAllInGenus InAct CausesIn esse c`). A created agent is read as an agent
other than it whose being it causes. Being applied to act is read as being moved
in some respect, in the broad sense of motion as reduction from potency to act
(*prima via*). Who moves it is not formalized; only that it is moved.

`CausesIn c y esse` is the cause of being (*esse*), as giving and preserving it,
not the cause of becoming (a father is a cause of his son's coming to be, not of
his being).

Source: Thomas Aquinas, *Summa theologiae* I q.105 a.5 co. and ad 3 (English
Dominican translation, 1920).
-/
def CausedAgentIsMovedToActReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ c y, CausesAllInGenus InAct CausesIn esse c → y ≠ c → CausesIn c y esse →
    (∃ x r, MovesIn y x r) → ∃ r', MovedIn y r'

end TruthCore.Latin.Aquinas.SummaTheologiae
