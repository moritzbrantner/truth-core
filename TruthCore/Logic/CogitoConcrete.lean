import TruthCore.Logic.CogitoSubject
import TruthCore.German.Kant.CosmologicalInference
import TruthCore.Alternatives.ActPotencyRegress

/-!
From an actual thought to an inhabited actual world, and to the prima via's
observation premise (#536). Source-free and stipulative: nothing here is
attributed to Descartes, Aristotle or Aquinas, and nothing shows that any
thought actually occurs.

The Cogito trunk is reused unchanged from #532
(`TruthCore.Logic.CogitoSubject`): `ThoughtOccurs Occurs` (O) and the bearer
principle `EveryThoughtHasSubject Occurs Bears` (B). The issue's `Realizes e b`
is #532's `Bears b e`, with the bearer drawn from the candidate domain `E` of
the Kant/#487 signature `Ontic W E`. A bearer is a bearer only: not a
substance, an enduring or immaterial self, or a person.

Two forks leave the trunk.

* **Concrete fork** (#487's population hypothesis). Two separate open bridges:
  every bearer of an occurring thought is concrete (C), and every such bearer
  exists at the selected world `w₀` (E). Together with O and B they give
  `InhabitedConcreteAt m concrete w₀`, which has the shape of #487's
  `PopulatedConcreteAt` (branch `codex/487-necessary-concrete-root`, not on
  `main`): `∃ b, concrete b ∧ m.ExistsAt w₀ b`. `w₀` is a complete world
  (history) of the frame, not a time; that it is the actual one is an
  interpretation of the argument, not a Lean fact. `concrete` is an
  unconstrained, world-independent predicate on the candidate domain, as on
  the #487 branch; no causal, spatiotemporal or material criterion is built in.
* **Motion fork** (root path). One open bridge: every bearer of an occurring
  thought opines that thought's content (OB). With the existing open premise
  `OpiningIsBeingMovedReading` (`STMT-OPINION-IS-A-MOTION`) it gives the prima
  via's `SomethingIsMovedReading`, whose Lean content is only `∃ x r, MovedIn x r`.
  Concreteness and world-indexed existence are not needed for that type.

The event route, in which an occurring episode is itself a concrete actual
entity through an explicit `embed : Episode → E`, is stated as
`OccurringEpisodeIsActualConcrete`. Its consequent is the inhabited-world
conclusion at the witness `embed e`, so any proof from it is a transcription
(AGENTS.md invariant 16); it is used here only in a model showing that the
bearer route is not necessary for population.
-/
namespace TruthCore.Logic.CogitoConcrete

open TruthCore.Logic.CogitoSubject
open TruthCore.German.Kant.CosmologicalInference (Ontic)

variable {W E Episode : Type}

/-- Some candidate is concrete and exists at world `w`: population of `w` by a
concrete being, as opposed to mere membership in the candidate domain or mere
inhabitation of the world type. Same shape as #487's `PopulatedConcreteAt`. -/
def InhabitedConcreteAt (m : Ontic W E) (concrete : E → Prop) (w : W) : Prop :=
  ∃ b, concrete b ∧ m.ExistsAt w b

/-- Bridge C: every bearer of an occurring thought is concrete. An open
ontological thesis; an idealist, an event theorist or a Platonist about
contents may each deny it for their own reasons. -/
def EveryBearerIsConcrete (Occurs : Episode → Prop) (Bears : E → Episode → Prop)
    (concrete : E → Prop) : Prop :=
  ∀ b e, Occurs e → Bears b e → concrete b

/-- Bridge E: every bearer of an occurring thought exists at world `w`. Open:
`Occurs` is not world-indexed, so this is the separate step from actual
occurrence to existence in the selected complete world. -/
def EveryBearerExistsAt (m : Ontic W E) (Occurs : Episode → Prop)
    (Bears : E → Episode → Prop) (w : W) : Prop :=
  ∀ b e, Occurs e → Bears b e → m.ExistsAt w b

/-- Bridge OB: whoever bears an occurring thought opines that thought's
content. Restricts the selected episodes to judgings or appearings with a
propositional content (`DEF-OPINING`); a willing or a non-propositional
episode would falsify it. -/
def BorneThoughtIsOpining (Occurs : Episode → Prop) (Bears : E → Episode → Prop)
    (Opines : E → Prop → Prop) (content : Episode → Prop) : Prop :=
  ∀ b e, Occurs e → Bears b e → Opines b (content e)

/-- The event route: each occurring episode, embedded in the candidate domain,
is concrete and exists at `w`. Its consequent already is the inhabited-world
conclusion at a witness; recorded for the event-route model only. -/
def OccurringEpisodeIsActualConcrete (m : Ontic W E) (concrete : E → Prop)
    (Occurs : Episode → Prop) (embed : Episode → E) (w : W) : Prop :=
  ∀ e, Occurs e → concrete (embed e) ∧ m.ExistsAt w (embed e)

/-- A one-world, one-candidate signature over `Unit`, with the supplied
existence extension. Used by the controls. -/
def unitOntic (ex : Prop) : Ontic Unit Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => ex
  Causes := fun _ _ _ => False

/-! ## Omission controls, concrete fork -/

/-- O omitted: no thought occurs; B, C and E hold vacuously, and no concrete
being exists at the world. -/
def NoThoughtControl : Prop :=
  ∃ (m : Ontic Unit Unit) (concrete : Unit → Prop) (Occurs : Unit → Prop)
    (Bears : Unit → Unit → Prop),
    ¬ ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      EveryBearerIsConcrete Occurs Bears concrete ∧
      EveryBearerExistsAt m Occurs Bears () ∧ ¬ InhabitedConcreteAt m concrete ()

/-- B omitted: a thought occurs but has no bearer; C and E hold vacuously, and
no concrete being exists at the world. -/
def BearerlessControl : Prop :=
  ∃ (m : Ontic Unit Unit) (concrete : Unit → Prop) (Occurs : Unit → Prop)
    (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ ¬ EveryThoughtHasSubject Occurs Bears ∧
      EveryBearerIsConcrete Occurs Bears concrete ∧
      EveryBearerExistsAt m Occurs Bears () ∧ ¬ InhabitedConcreteAt m concrete ()

/-- C omitted: an occurring thought is borne by a being that exists at the
world but is not concrete (an abstract or content-level realizer). -/
def AbstractBearerControl : Prop :=
  ∃ (m : Ontic Unit Unit) (concrete : Unit → Prop) (Occurs : Unit → Prop)
    (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      ¬ EveryBearerIsConcrete Occurs Bears concrete ∧
      EveryBearerExistsAt m Occurs Bears () ∧ ¬ InhabitedConcreteAt m concrete ()

/-- E omitted: an occurring thought is borne by a concrete candidate that does
not exist at the world. -/
def NonexistentBearerControl : Prop :=
  ∃ (m : Ontic Unit Unit) (concrete : Unit → Prop) (Occurs : Unit → Prop)
    (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      EveryBearerIsConcrete Occurs Bears concrete ∧
      ¬ EveryBearerExistsAt m Occurs Bears () ∧ ¬ InhabitedConcreteAt m concrete ()

/-- Event route without a bearer: an occurring episode is itself (through
`embed`) a concrete entity existing at the world, and the bearer relation is
empty, so B fails while the world is inhabited. The bearer route is sufficient
with C and E, not necessary. Types: one episode, one candidate, `embed` the
unique map. -/
def EventWithoutBearerModel : Prop :=
  ∃ (m : Ontic Unit Unit) (concrete : Unit → Prop) (Occurs : Unit → Prop)
    (Bears : Unit → Unit → Prop) (embed : Unit → Unit),
    ThoughtOccurs Occurs ∧ OccurringEpisodeIsActualConcrete m concrete Occurs embed () ∧
      ¬ EveryThoughtHasSubject Occurs Bears ∧ InhabitedConcreteAt m concrete ()

/-! ## Omission controls, motion fork -/

/-- O omitted: OB, B and opinion-as-motion hold, nothing is moved. -/
def NoThoughtMotionControl : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop) (Opines : Unit → Prop → Prop)
    (MovedIn : Unit → Unit → Prop),
    ¬ ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      BorneThoughtIsOpining Occurs Bears Opines (fun _ => True) ∧
      TruthCore.Alternatives.ActPotencyRegress.OpiningIsBeingMovedReading
        MovedIn Opines (fun _ => ()) ∧
      ¬ TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading MovedIn

/-- B omitted: a thought occurs without a bearer, nothing is moved. -/
def BearerlessMotionControl : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop) (Opines : Unit → Prop → Prop)
    (MovedIn : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ ¬ EveryThoughtHasSubject Occurs Bears ∧
      BorneThoughtIsOpining Occurs Bears Opines (fun _ => True) ∧
      TruthCore.Alternatives.ActPotencyRegress.OpiningIsBeingMovedReading
        MovedIn Opines (fun _ => ()) ∧
      ¬ TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading MovedIn

/-- OB omitted: a borne thought occurs, but its bearer opines nothing (a
non-propositional episode); opining is motion, and nothing is moved. -/
def NonOpiningThoughtControl : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop) (Opines : Unit → Prop → Prop)
    (MovedIn : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      ¬ BorneThoughtIsOpining Occurs Bears Opines (fun _ => True) ∧
      TruthCore.Alternatives.ActPotencyRegress.OpiningIsBeingMovedReading
        MovedIn Opines (fun _ => ()) ∧
      ¬ TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading MovedIn

/-- Opinion-as-motion omitted: the bearer opines, and nothing is moved (the
McTaggart-style position that appearings occur without motion). -/
def UnmovedOpinerControl : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop) (Opines : Unit → Prop → Prop)
    (MovedIn : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      BorneThoughtIsOpining Occurs Bears Opines (fun _ => True) ∧
      ¬ TruthCore.Alternatives.ActPotencyRegress.OpiningIsBeingMovedReading
        MovedIn Opines (fun _ => ()) ∧
      ¬ TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading MovedIn

/-- All controls: each premise of each fork is needed, and the bearer route is
not the only route to population. Formal interpretations only, not
metaphysical possibility certificates. -/
def OmissionControls : Prop :=
  NoThoughtControl ∧ BearerlessControl ∧ AbstractBearerControl ∧
    NonexistentBearerControl ∧ EventWithoutBearerModel ∧
    NoThoughtMotionControl ∧ BearerlessMotionControl ∧
    NonOpiningThoughtControl ∧ UnmovedOpinerControl

end TruthCore.Logic.CogitoConcrete
