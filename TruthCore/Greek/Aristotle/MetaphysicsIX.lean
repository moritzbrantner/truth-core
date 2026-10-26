/-!
Aristotle, *Metaphysics* IX (Θ).6, 1048a25-b9: actuality defined by analogy and
by contrast with potency.

The vocabulary is the act/potency vocabulary of the *prima via*
(`TruthCore.Latin.Aquinas.SummaTheologiae`, `Question2.Article3`), so that the
reading can be compared with Aquinas' premises directly:

* `InAct x r` — `x` is actually `r` (ἐνεργείᾳ), as the one contemplating is
  actually a knower, or the Hermes cut out of the wood is actually a Hermes.
* `InPotency x r` — `x` is potentially `r` (δυνάμει).
* `CanBe x r` — `x` is able to be `r` (δυνατός), as the knower who is not
  contemplating is able to contemplate. A new primitive: Θ.6 distinguishes
  being able (the knower *if he is able to contemplate*) from being potentially.

Source witness: Ross/Perseus Greek text, passage `ARIST-MET-IX-6`.
CTS work: `urn:cts:greekLit:tlg0086.tlg025`.
-/

namespace TruthCore.Greek.Aristotle.Metaphysics

universe u v

/-- Potency in a respect is an unactualized ability for it (*Metaphysics* Θ.6,
1048a30-35): "actuality is the thing's existing not in the way in which we say
it exists potentially; we say potentially, e.g., the Hermes in the wood ... and
the knower who is not contemplating, if he is able to contemplate" (ἔστι δὴ
ἐνέργεια τὸ ὑπάρχειν τὸ πρᾶγμα μὴ οὕτως ὥσπερ λέγομεν δυνάμει ... καὶ
ἐπιστήμονα καὶ τὸν μὴ θεωροῦντα, ἂν δυνατὸς ᾖ θεωρῆσαι).

Read as a biconditional in each respect: `x` is potentially `r` exactly when it
is able to be `r` and is not actually `r`. Both conditions come from the
examples: the knower is not contemplating, and he is able to. The analogy that
follows (1048a35-b6) is not formalized, nor the two kinds of act it
distinguishes (motion to power, substance to matter).

This is a *definitional analysis*. Taken as a definition of `InPotency`, it
makes the *prima via*'s non-simultaneity premise analytic; the formal fact
`ActPotencyDefinitionalAnalysesConservative` shows that it is also no stronger
than that premise as long as `CanBe` is constrained by nothing else.

Source: Aristotle, *Metaphysics* IX.6, 1048a30-35 (Bekker pagination).
-/
def PotencyIsUnactualizedCapacityReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency CanBe : Being → Respect → Prop) : Prop :=
  ∀ x r, InPotency x r ↔ CanBe x r ∧ ¬ InAct x r

end TruthCore.Greek.Aristotle.Metaphysics
