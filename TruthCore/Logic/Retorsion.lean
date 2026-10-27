/-!
One retorsion schema for global underminers (#515).

A *global underminer* asserts that nothing has some feature `X` (nothing is
moved, nothing changes, nothing is known, ...), where its own assertion or
appearance seems to require `X`. The schema separates the three things a
retorsion needs, so that each instance states exactly which one it supplies
and which one is open:

* `Underminer.Performs a p` — agent `a` performs content `p`: asserts it,
  opines it, or has it appear. Which act is meant is fixed per instance.
* `Underminer.Feature w` — witness `w` has the feature `X`; the underminer's
  `thesis` is a content that `denies` every witness.
* `Underminer.Link trace` — the **presupposition link**: every performance of
  any content by any agent yields, through `trace`, a witness of the feature.
  This is the philosophical premise of every instance; the schema never
  supplies it.

`position_inconsistent` proves that the held position (thesis true and
performed by someone) is inconsistent given the link. The proof is a two-step
derivation: apply the link to the performance of the thesis, then the thesis's
own denial. Its consequent is a feature of a witness, not the conclusion, so it
is not a single-application transcription in the sense of AGENTS.md
invariant 16; but its philosophical content lies wholly in each instance's
link, and its value is reuse. `thesis_false_of_performance` records that only
*some* performance is used: the self-application is incidental to the logic.
-/

namespace TruthCore.Logic.Retorsion

/-- A global underminer, as a typed record: a performance relation on agents and
contents, a feature of witnesses, and a thesis that denies the feature of every
witness. `denies` is the requirement that the thesis asserts ¬X with
X := ∃ w, Feature w; it is a proof obligation of each instance's construction. -/
structure Underminer (Agent W : Type) where
  Performs : Agent → Prop → Prop
  Feature : W → Prop
  thesis : Prop
  denies : thesis → ∀ w, ¬ Feature w

variable {Agent W : Type}

/-- The presupposition link: every performance yields, through `trace`, a
witness of the feature. -/
def Underminer.Link (U : Underminer Agent W) (trace : Agent → Prop → W) : Prop :=
  ∀ a p, U.Performs a p → U.Feature (trace a p)

/-- The thesis is held: some agent performs it. -/
def Underminer.Held (U : Underminer Agent W) : Prop :=
  ∃ a, U.Performs a U.thesis

/-- The held position: the thesis is true and someone performs it. -/
def Underminer.Position (U : Underminer Agent W) : Prop :=
  U.thesis ∧ U.Held

/-- Only some performance is needed: given the link, any performance at all
refutes the thesis. -/
theorem Underminer.thesis_false_of_performance (U : Underminer Agent W)
    {trace : Agent → Prop → W} (hLink : U.Link trace) (hSome : ∃ a p, U.Performs a p) :
    ¬ U.thesis := by
  intro hThesis
  obtain ⟨a, p, hPerf⟩ := hSome
  exact U.denies hThesis _ (hLink a p hPerf)

/-- Retorsion: given the presupposition link, the held position is
inconsistent. -/
theorem Underminer.position_inconsistent (U : Underminer Agent W)
    {trace : Agent → Prop → W} (hLink : U.Link trace) : ¬ U.Position := by
  intro ⟨hThesis, a, hPerf⟩
  exact U.denies hThesis _ (hLink a U.thesis hPerf)

/-- Retorsion, in the form an instance consumes: link and holding refute the
thesis. -/
theorem Underminer.thesis_false (U : Underminer Agent W)
    {trace : Agent → Prop → W} (hLink : U.Link trace) (hHeld : U.Held) : ¬ U.thesis :=
  fun hThesis => U.position_inconsistent hLink ⟨hThesis, hHeld⟩

/-- Advertised schema: for every typed underminer and trace, the presupposition
link makes the held position inconsistent. The link stays inside the
quantified conditional, so verifying the schema closes no instance's link. -/
def RetorsionSchema : Prop :=
  ∀ (Agent W : Type) (U : Underminer Agent W) (trace : Agent → Prop → W),
    U.Link trace → ¬ U.Position

end TruthCore.Logic.Retorsion
