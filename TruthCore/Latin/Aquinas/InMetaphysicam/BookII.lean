/-!
An unattributed premise motivated by Thomas Aquinas, *Sententia libri Metaphysicae*
II, lect. 2 n. 11, on *Metaphysics* II.2, 994a1-2: the proof that first
philosophy considers what is most true supposes that there are first causes,
and that would be removed if causes went on to infinity (*Hoc autem tolleretur
si causae in infinitum procederent. Tunc enim non essent aliquae primae
causae*). Aristotle's thesis, in Aquinas' paraphrase: *quod sit aliquod
principium esse et veritatis rerum; et quod causae existentium non sunt
infinitae, nec procedendo in directum secundum unam aliquam speciem causae*.

**Vocabulary.** Beings, respects and `CausesIn c x r` (`c` causes `x`'s being
`r`, `DEF-CAUSE-OF-PERFECTION`) are those of the *quarta via* readings
(`TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus`). Nothing new is
primitive here.

Source witness: Corpus Thomisticum Latin page, pinned as web snapshot passage
`AQUINAS-IN-METAPH-II-L2`.
-/

namespace TruthCore.Latin.Aquinas.InMetaphysicam

universe u v

/-- No infinite regress of causes of one perfection: for every perfection `r`,
the relation "`c` is a cause, distinct from `x`, of `x`'s being `r`" is
well-founded (Lean's `WellFounded`: every being is accessible, so there is no
infinite backward series `x₀ ← c₁ ← c₂ ← …` of distinct causes of `r`, and no
cycle of them).

Unattributed strengthening, not a reading of the lecture: the source denies
an infinite series *in directum* within one species of cause (material,
efficient, final, formal) and infinitely many species. This premise indexes
the line by the perfection caused instead, so it also excludes a series of
causes of one perfection that alternates between species, which the sentence
does not address; individually well-founded causal modes can have a
non-well-founded union. The lecture (and the secunda via) support it only
(relation `REL-AQUINAS-ST-I-Q2-A3-SECUNDA-VIA-SUPPORTS-NO-INFINITE-REGRESS-OF-CAUSES-OF-A-PERFECTION`). Self-causation (`c = x`) is outside the
relation. Nothing here makes the first cause unique, maximal or God.

Source motivation: Thomas Aquinas, *In Metaphysicam* II, lect. 2 n. 11. -/
def NoInfiniteRegressOfCausesOfAPerfectionReading {Being : Sort u}
    {Respect : Sort v} (CausesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ r, WellFounded (fun c x => c ≠ x ∧ CausesIn c x r)

end TruthCore.Latin.Aquinas.InMetaphysicam
