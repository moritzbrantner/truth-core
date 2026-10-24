/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.105 a.5 co.
and ad 3 (*utrum Deus operetur in omni operante*).

Basis: the English Dominican translation (2nd rev. ed. 1920), pinned as the web
snapshot `AQUINAS-ST-I-Q105-A5-EN`; SCTA has no Latin text for this question.
The reading is a candidate for upgrade once a pinned Latin witness exists.

Vocabulary as in the *prima via* (`MovedIn`, `MovesIn`) and the *quarta via*
(`CausesIn`, `esse`), with `God : Being → Prop` marking the one the article calls
God.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Every created agent acts as moved to act by God: "God not only moves things to
operate, as it were applying their forms and powers to operation ...; but He also
gives created agents their forms and preserves them in being" (co., third way);
"God not only gives things their form, but He also preserves them in existence,
and applies them to act" (ad 3); "all agents act in virtue of God Himself" (co.,
second way).

`God g` marks the one the article calls God; the reading says nothing about
which being that is, and in particular does not identify God with whatever
causes the being of all other things (that identification is the separate open
premise `TruthCore.Case.Catholicism.MaximeEnsIsGod`). A created agent is read as
an agent other than God whose being God causes (gives and preserves).
Being applied to act is read as being moved in some respect, in the broad sense
of motion as reduction from potency to act (*prima via*); that the mover is God
is not formalized, only that the agent is moved.

`CausesIn g y esse` is the cause of being (*esse*), as giving and preserving it,
not the cause of becoming.

Source: Thomas Aquinas, *Summa theologiae* I q.105 a.5 co. and ad 3 (English
Dominican translation, 1920).
-/
def CreatedAgentIsAppliedToActByGodReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop) : Prop :=
  ∀ g y, God g → y ≠ g → CausesIn g y esse →
    (∃ x r, MovesIn y x r) → ∃ r', MovedIn y r'

end TruthCore.Latin.Aquinas.SummaTheologiae
