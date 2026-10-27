/-!
An assertion-token retorsion for #509. The actual performance of a token is
distinct from the truth of its content. In particular, an *unperformed* denial
can be true in an empty-episode interpretation. Nothing here establishes that
any episode occurs in the actual world or that any episode involves change.
-/

namespace TruthCore.Logic.PerformedDenial

universe u

/-- The claim that no episode of the selected type occurs. The domain need not
be inhabited and `Occurs` is an unconstrained interpretation. -/
def NoEpisodeOccurs {Episode : Sort u} (Occurs : Episode → Prop) : Prop :=
  ¬ ∃ e, Occurs e

/-- An *accurate performed denial* of the claim that no episode occurs: the
denying token occurs, is used to deny all such episodes, and its denial content
is true. `DeniesAll` alone does not assert truth or actual performance. -/
def AccuratePerformedDenial {Episode : Sort u} (Occurs DeniesAll : Episode → Prop) : Prop :=
  ∃ e, Occurs e ∧ DeniesAll e ∧ NoEpisodeOccurs Occurs

/-- Negation of an accurate performed universal denial, not negation of an
unperformed thought or false utterance. -/
def AccurateDenialImpossible {Episode : Sort u} (Occurs DeniesAll : Episode → Prop) : Prop :=
  ¬ AccuratePerformedDenial Occurs DeniesAll

/-- The unperformed empty-episode interpretation is compatible with the truth
of the denial. This model says nothing about the actual world. -/
def EmptyEpisodeControl : Prop :=
  ∃ (Occurs DeniesAll : Unit → Prop),
    NoEpisodeOccurs Occurs ∧ DeniesAll () ∧ ¬ Occurs ()

/-- A single occurring episode can be interpreted over a one-point time type
with one constant state; occurrence alone does not entail successive states. -/
def StaticEpisodeControl : Prop :=
  ∃ (Occurs : Unit → Prop) (StateAt : Unit → Bool),
    Occurs () ∧ ¬ ∃ t₁ t₂ : Unit, StateAt t₁ ≠ StateAt t₂

end TruthCore.Logic.PerformedDenial
