module

/-!
*Über Gewißheit* on doubt and what stands fast (#1010).

§341: "die *Fragen*, die wir stellen, und unsre *Zweifel* beruhen darauf, daß
gewisse Sätze vom Zweifel ausgenommen sind, gleichsam die Angeln, in welchen
jene sich bewegen." §115: "Wer an allem zweifeln wollte, der würde auch nicht
bis zum Zweifel kommen. Das Spiel des Zweifelns selbst setzt schon die
Gewißheit voraus."

Vocabulary (stipulative, `DEF-DOUBTED-SENTENCE`): `Sentence` ranges over what
can be asserted or doubted; `Doubted s` says that `s` is doubted by the doubter
in question. "Exempt from doubt" is `¬ Doubted s`. Nothing here says that an
exempt sentence is known, true or justified: that is exactly what the hinge
readings dispute (`DISAMB-HINGE-STATUS`).
-/

@[expose] public section

namespace TruthCore.German.Wittgenstein.OnCertainty

/-- §341, doubt presupposes exemption (`STMT-OC-DOUBT-RESTS-ON-EXEMPT-SENTENCES`):
whenever a sentence is doubted, some sentence is exempt from doubt.

Weakest reading: it says only that some sentence is exempt, not which one, not
that it is the same for every doubt, and not that the exempt sentence is known
or true (§151: Moore does not *know* what he claims, but it stands fast for
him). -/
def DoubtRestsOnExemptionReading {Sentence : Type} (Doubted : Sentence → Prop) : Prop :=
  ∀ s, Doubted s → ∃ h, ¬ Doubted h

/-- The universal doubter of §115 (`STMT-UNIVERSAL-DOUBT`): some sentence is
doubted, and every sentence is doubted ("an allem zweifeln"). The first conjunct
keeps the thesis from being vacuously met when nothing is doubted ("bis zum
Zweifel kommen"). -/
def UniversalDoubtReading {Sentence : Type} (Doubted : Sentence → Prop) : Prop :=
  (∃ s, Doubted s) ∧ ∀ s, Doubted s

/-- Conclusion (`STMT-UNIVERSAL-DOUBT-FAILS`): the universal doubter's position
does not hold. -/
def UniversalDoubtFails {Sentence : Type} (Doubted : Sentence → Prop) : Prop :=
  ¬ UniversalDoubtReading Doubted

end TruthCore.German.Wittgenstein.OnCertainty
