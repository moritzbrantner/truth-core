import TruthCore.Comparison.ProblemOfEvil
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels

/-!
A concrete model of the background, the Catholic theory, and evil.

The motion part is the strong model of #151 (`strongModel`), in which all seven
strong *prima via* premises hold: `g` moves `f` and is moved in no respect, `f`
moves `x`. On top of it:

* `g` is God: the first mover moved by none. It has every perfection, lacks
  none due to it, can eliminate the evil in every being, and so is supremely
  good (has every perfection) and omnipotent (can eliminate every evil).
* `f` (the lion of q.48 a.2 ad 3) has the perfection `life`, which is due to it.
* `x` (the ass) lacks `life`, which is due to it: a privation, so there is evil
  in `x`, and only in `x`.
* God draws good out of the evil in `x`: the lion's life (`f` has `life`).
* Sentences: "there is evil" is true exactly when something is evil; "the
  first mover is unmoved" is true exactly when `g` is moved in no respect.

Every predicate is a concrete extension defined by case analysis; none is a
constant placeholder. The definitions are non-overlapping matches, so no proof
needs `propext`.
-/

namespace TruthCore.Results.Comparison.ProblemOfEvil.CatholicConsistentWithEvil
open TruthCore.Comparison.ProblemOfEvil
open TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels

inductive WPerfection | life
inductive WSentence | thereIsEvil | firstMoverUnmoved

/-- `g` and `f` have life; `x` does not. -/
def wHas : StrongBeing → WPerfection → Prop
  | .g, .life => True
  | .f, .life => True
  | .x, .life => False

/-- Life is due to the two creatures, not to God. -/
def wDue : StrongBeing → WPerfection → Prop
  | .g, .life => False
  | .f, .life => True
  | .x, .life => True

def wEvil : StrongBeing → Prop
  | .g => False
  | .f => False
  | .x => True

def wGod : StrongBeing → Prop
  | .g => True
  | .f => False
  | .x => False

/-- Only `g` can eliminate evil, and it can eliminate the evil in any being. -/
def wCanEliminate : StrongBeing → StrongBeing → Prop
  | .g, _ => True
  | .f, _ => False
  | .x, _ => False

def wSupremelyGood (b : StrongBeing) : Prop := ∀ p, wHas b p
def wOmnipotent (b : StrongBeing) : Prop := ∀ y, wCanEliminate b y

/-- `g` brings the lion's life out of the ass's evil; nothing else. -/
def wDrawsGoodFrom : StrongBeing → StrongBeing → StrongBeing → WPerfection → Prop
  | .g, .x, .f, .life => True
  | .g, .x, .g, _ => False
  | .g, .x, .x, _ => False
  | .g, .g, _, _ => False
  | .g, .f, _, _ => False
  | .f, _, _, _ => False
  | .x, _, _, _ => False

def wHolds : WSentence → Prop
  | .thereIsEvil => ∃ b, wEvil b
  | .firstMoverUnmoved => ∀ r, ¬ strongMovedIn .g r

def witness : Sig where
  motion := strongModel
  Perfection := WPerfection
  Sentence := WSentence
  Has := wHas
  Due := wDue
  GoodIn := wHas
  Evil := wEvil
  God := wGod
  SupremelyGood := wSupremelyGood
  Omnipotent := wOmnipotent
  CanEliminate := wCanEliminate
  DrawsGoodFrom := wDrawsGoodFrom
  Holds := wHolds
  evilPremise := .thereIsEvil

theorem witnessPrivation : ∀ b, wEvil b ↔ ∃ p, wDue b p ∧ ¬ wHas b p
  | .g => ⟨False.elim, fun ⟨.life, hDue, _⟩ => hDue⟩
  | .f => ⟨False.elim, fun ⟨.life, _, hLacks⟩ => hLacks trivial⟩
  | .x => ⟨fun _ => ⟨.life, trivial, id⟩, fun _ => trivial⟩

theorem witnessIdentification :
    ∀ b, ((∃ y r, strongMovesIn b y r) ∧ ∀ r, ¬ strongMovedIn b r) → wGod b
  | .g, _ => trivial
  | .f, ⟨_, hUnmoved⟩ => hUnmoved .other trivial
  | .x, ⟨⟨_, _, hMoves⟩, _⟩ => hMoves

theorem witnessAttributes : ∀ b, wGod b → wSupremelyGood b ∧ wOmnipotent b
  | .g, _ => ⟨fun | .life => trivial, fun _ => trivial⟩
  | .f, h => False.elim h
  | .x, h => False.elim h

theorem witnessDrawsGood :
    ∀ a b, wGod a → wEvil b → ∃ y p, wHas y p ∧ wDrawsGoodFrom a b y p
  | .g, .x, _, _ => ⟨.f, .life, trivial, trivial⟩
  | .g, .g, _, h => False.elim h
  | .g, .f, _, h => False.elim h
  | .f, _, h, _ => False.elim h
  | .x, _, h, _ => False.elim h

theorem catholicConsistentWithEvil : CatholicTheoryConsistentWithEvil :=
  let ⟨hSense, hPotency, hAct, hReduction, hNotBoth, hPerSe, hRegress⟩ := strongModel_premises
  ⟨witness,
    (fun _ b hOmni _ => hOmni b),
    ⟨fun _ _ => Iff.rfl, witnessPrivation, fun hEvil => hEvil,
      ⟨.x, .life, trivial, id⟩,
      hSense, hPotency, hAct, hReduction, hNotBoth, hPerSe, hRegress,
      witnessIdentification,
      witnessAttributes,
      witnessDrawsGood⟩,
    ⟨.x, trivial⟩⟩

end TruthCore.Results.Comparison.ProblemOfEvil.CatholicConsistentWithEvil
