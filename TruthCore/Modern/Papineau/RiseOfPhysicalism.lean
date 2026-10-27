/-!
Readings from David Papineau, "The Rise of Physicalism", in *Physicalism and
Its Discontents* (2001), pp. 3–36.

Source witness: the author-hosted PDF, hash-pinned as a `web_snapshot`
(passages PAPINEAU-RISE-PHYSICALISM-3-12 and PAPINEAU-RISE-PHYSICALISM-13-33).

Papineau's vocabulary is his own and is kept apart from the case's act/potency
vocabulary. Its relata are *occurrences* (he reads causal relata as facts or
property instantiations, p. 10), not beings, and its "physical" is his
stipulated sense (pp. 12–13), not Aristotle's respects of physical motion. Any
passage to the case vocabulary is an explicit, unattributed bridge
(`TruthCore.Alternatives.PhysicalCompleteness`).
-/

namespace TruthCore.Modern.Papineau.RiseOfPhysicalism

/-- The completeness of physics (p. 8, "a more precise version"): "All physical
effects are fully determined by law by prior physical occurrences." Papineau
endorses it at the end of the chapter (pp. 32–33): there is "now good reason to
believe the empirical thesis that all physical effects are due to physical
causes", a premise "fully established by over a century of empirical
research", while granting that it is empirical and not certain.

* `Physical e`: `e` is physical in Papineau's sense, specifiable without the
  special (mental, biological, ...) vocabulary at issue (pp. 12–13,
  DEF-PAPINEAU-PHYSICAL).
* `IsEffect e`: `e` is an effect. The thesis is about physical *effects*; it
  does not say that every physical occurrence has a cause.
* `Prior c e`: `c` is earlier than `e`.
* `FullyDeterminedByLaw S e`: the occurrences satisfying `S` fully determine `e`
  by law (DEF-PAPINEAU-LAWFUL-DETERMINATION). It is abstract, so it also covers
  note 2's chance version ("the chances of all physical occurrences are fully
  determined by prior physical occurrences").

The thesis is "purely a doctrine about the structure of the physical realm"
(p. 8): it says nothing about nonphysical things, and it is not physicalism.
-/
def CompletenessOfPhysicsReading {Occurrence : Type}
    (Physical IsEffect : Occurrence → Prop)
    (Prior : Occurrence → Occurrence → Prop)
    (FullyDeterminedByLaw : (Occurrence → Prop) → Occurrence → Prop) : Prop :=
  ∀ e, Physical e → IsEffect e → FullyDeterminedByLaw (fun c => Physical c ∧ Prior c e) e

end TruthCore.Modern.Papineau.RiseOfPhysicalism
