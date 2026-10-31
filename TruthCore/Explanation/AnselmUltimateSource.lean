import TruthCore.Explanation.WellFoundedSource
import Mathlib.Basic.ExistsUnique

/-!
Analyst reduction of Tapp 2014 §6's Monologion reconstruction, not a new claim
that Anselm states these typed world-relative predicates. Context reuses the
existing existence-PSR Model; no explanation or efficient cause is identified
with the new per-aliquid relation. Through is TARGET-first, SOURCE-second.
No transitivity, antisymmetry, WF or three-case axiom is built into the data.
All substantive interfaces are separate open predicates. See
 docs/notes/necessary-simple-plurality.md for source/application boundaries.
-/
namespace TruthCore.Explanation.AnselmUltimateSource
open TruthCore.Explanation.ExistencePSR

structure Context (W B : Type) where
  reality : Model W B
  through : W → B → B → Prop
  selfPowerFrom : W → B → B → Prop

/-- Existing root relative to through: no DISTINCT source for this bearer.
A self-link is permitted and is not efficient self-production by definition. -/
def RootAt (m : Context W B) (w : W) (y : B) : Prop :=
  m.reality.ontic.ExistsAt w y ∧ ∀ z, m.through w y z → z = y

/-- Tapp's EP+ shape, with orientation target then source. -/
def UltimateThroughAt (m : Context W B) (w : W) (x y : B) : Prop :=
  m.through w x y ∧ ∀ z, m.through w y z → z = y

/-- Source actuality is explicit. It follows from Tapp's endpoint-factivity
premise when such a source is supplied; it is not inferred from a type name. -/
def UltimateSourceAt (m : Context W B) (w : W) (y : B) : Prop :=
  m.reality.ontic.ExistsAt w y ∧ ∃ x, UltimateThroughAt m w x y

/-- Only source-side endpoint actuality is needed for existence extraction;
no target-side factivity is required by the theorem. -/
def SourcesActualAt (m : Context W B) (w : W) : Prop :=
  ∀ x y, m.through w x y → m.reality.ontic.ExistsAt w y

def CoverageAt (m : Context W B) (w : W) : Prop :=
  ∀ x, m.reality.ontic.ExistsAt w x → ∃ y, m.through w x y

/-- EP+3 is substantive ultimate availability, not a proved regress exclusion. -/
def UltimateAvailableAt (m : Context W B) (w : W) : Prop :=
  ∀ x y, m.through w x y → ∃ z, UltimateThroughAt m w x z

/-- HVEP1: a numerically ONE source of self-existence power for every self-link.
A common predicate or a set of joint conditions does not supply this witness. -/
def SharedSelfPowerAt (m : Context W B) (w : W) : Prop :=
  ∃ c, ∀ x, m.through w x x → m.selfPowerFrom w x c

/-- HVEP2: receiving that power from c makes the bearer through c.
Neither truth nor efficient production is built into the power relation. -/
def PowerGivesThroughAt (m : Context W B) (w : W) : Prop :=
  ∀ x c, m.selfPowerFrom w x c → m.through w x c

def AtMostOneUltimateSourceAt (m : Context W B) (w : W) : Prop :=
  ∀ x y, UltimateSourceAt m w x → UltimateSourceAt m w y → x = y

def SomeUltimateSourceAt (m : Context W B) (w : W) : Prop :=
  ∃ x, UltimateSourceAt m w x

def UniqueUltimateSourceAt (m : Context W B) (w : W) : Prop :=
  ∃! x, UltimateSourceAt m w x


/-- Universal at ONE actual world, retaining the same ultimate source for every
actual target; this is not universality across accessible worlds. -/
def UniversalUltimateSourceAt (m : Context W B) (w : W) (y : B) : Prop :=
  m.reality.ontic.ExistsAt w y ∧
    ∀ x, m.reality.ontic.ExistsAt w x → UltimateThroughAt m w x y

def UniqueUniversalUltimateSourceAt (m : Context W B) (w : W) : Prop :=
  ∃! y, UniversalUltimateSourceAt m w y

end TruthCore.Explanation.AnselmUltimateSource
