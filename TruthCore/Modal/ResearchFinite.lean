import TruthCore.Modal.ResearchFixture

/-! Deterministic finite semantics. Lists enumerate all worlds, including sinks.
Boolean evaluation is proved equal to the existing Prop semantics. -/
namespace TruthCore.Modal.ResearchFinite
open TruthCore.Modal.ResearchFixture

structure Model (W A : Type) where
  worlds : List W
  complete : ∀ w, w ∈ worlds
  edge : W → W → Bool
  atom : W → A → Bool

def Model.frame {W A : Type} (m : Model W A) : Frame W := ⟨fun w v => m.edge w v = true⟩
def Model.valuation {W A : Type} (m : Model W A) : Valuation W A :=
  fun w a => m.atom w a = true

def eval {W A : Type} (m : Model W A) (w : W) : Formula A → Bool
  | .atom a => m.atom w a
  | .falsum => false
  | .imp p q => !eval m w p || eval m w q
  | .box p => m.worlds.all (fun v => !m.edge w v || eval m v p)
  | .diamond p => m.worlds.any (fun v => m.edge w v && eval m v p)

private theorem orTrue (a b : Bool) : a || b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide
private theorem andTrue (a b : Bool) : a && b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide
private theorem notTrue (a : Bool) : !a = true ↔ a = false := by
  cases a <;> decide

private theorem allTrue {W : Type} (xs : List W) (f : W → Bool) :
    xs.all f = true ↔ ∀ w, w ∈ xs → f w = true := by
  induction xs with
  | nil =>
    constructor
    · intro _ w hw; cases hw
    · intro _; rfl
  | cons a xs ih =>
    constructor
    · intro h w hw
      have hh := (andTrue (f a) (xs.all f)).mp h
      cases hw with
      | head => exact hh.1
      | tail _ hw => exact ih.mp hh.2 w hw
    · intro h
      exact (andTrue _ _).mpr ⟨h a (.head xs), ih.mpr (fun w hw => h w (.tail a hw))⟩

private theorem anyTrue {W : Type} (xs : List W) (f : W → Bool) :
    xs.any f = true ↔ ∃ w, w ∈ xs ∧ f w = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; exact Bool.noConfusion h
    · rintro ⟨w, hw, _⟩; cases hw
  | cons a xs ih =>
    constructor
    · intro h
      cases (orTrue (f a) (xs.any f)).mp h with
      | inl ha => exact ⟨a, .head xs, ha⟩
      | inr ht =>
        obtain ⟨w, hw, hf⟩ := ih.mp ht
        exact ⟨w, .tail a hw, hf⟩
    · rintro ⟨w, hw, hf⟩
      apply (orTrue _ _).mpr
      cases hw with
      | head => exact .inl hf
      | tail _ hw => exact .inr (ih.mpr ⟨w, hw, hf⟩)

theorem eval_correct {W A : Type} (m : Model W A) (p : Formula A) (w : W) :
    eval m w p = true ↔ Holds m.frame m.valuation w p := by
  induction p generalizing w with
  | atom a => rfl
  | falsum =>
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; exact h.elim
  | imp p q hp hq =>
    constructor
    · intro h hP
      cases (orTrue _ _).mp h with
      | inl hn =>
        have he := (notTrue _).mp hn
        have ht := (hp w).mpr hP
        rw [he] at ht
        exact Bool.noConfusion ht
      | inr ht => exact (hq w).mp ht
    · intro h
      apply (orTrue _ _).mpr
      cases he : eval m w p with
      | false => exact .inl rfl
      | true => exact .inr ((hq w).mpr (h ((hp w).mp he)))
  | box p hp =>
    constructor
    · intro h v hv
      have hh := (allTrue _ _).mp h v (m.complete v)
      cases (orTrue _ _).mp hh with
      | inl hn =>
        have he := (notTrue _).mp hn
        change m.edge w v = false at he
        change m.edge w v = true at hv
        rw [he] at hv
        exact Bool.noConfusion hv
      | inr ht => exact (hp v).mp ht
    · intro h
      apply (allTrue _ _).mpr
      intro v _
      apply (orTrue _ _).mpr
      cases he : m.edge w v with
      | false => exact .inl rfl
      | true => exact .inr ((hp v).mpr (h v he))
  | diamond p hp =>
    constructor
    · intro h
      obtain ⟨v, _, hv⟩ := (anyTrue _ _).mp h
      have hh := (andTrue _ _).mp hv
      exact ⟨v, hh.1, (hp v).mp hh.2⟩
    · rintro ⟨v, he, ht⟩
      exact (anyTrue _ _).mpr ⟨v, m.complete v, (andTrue _ _).mpr ⟨he, (hp v).mpr ht⟩⟩

/-- All accessible witnesses in enumeration order; no random search. -/
def witnesses {W A : Type} (m : Model W A) (w : W) (p : Formula A) : List W :=
  m.worlds.filter (fun v => m.edge w v && eval m v p)

/-- Counterexample witnesses to □p. -/
def counterexamples {W A : Type} (m : Model W A) (w : W) (p : Formula A) : List W :=
  m.worlds.filter (fun v => m.edge w v && !eval m v p)

/-- A branching root with a terminal successor; no modal-system classification here. -/
def branching : Model Bool Unit where
  worlds := [false, true]
  complete := by
    intro w; cases w with
    | false => exact .head _
    | true => exact .tail _ (.head _)
  edge := fun w v => !w || v
  atom := fun w _ => !w

/-- A root with no successors, included to expose vacuous box truth. -/
def deadEnd : Model Unit Unit where
  worlds := [()]
  complete := by intro w; cases w; exact .head _
  edge := fun _ _ => false
  atom := fun _ _ => false

/-- Two labels with exactly the same fixed-language valuation and universal edges. -/
def duplicates : Model Bool Unit where
  worlds := [false, true]
  complete := by
    intro w; cases w with
    | false => exact .head _
    | true => exact .tail _ (.head _)
  edge := fun _ _ => true
  atom := fun _ _ => true

theorem duplicates_constant (p : Formula Unit) :
    Holds duplicates.frame duplicates.valuation false p ↔
    Holds duplicates.frame duplicates.valuation true p := by
  induction p with
  | atom a => rfl
  | falsum => rfl
  | imp p q hp hq =>
    constructor
    · intro h ht; exact hq.mp (h (hp.mpr ht))
    · intro h hf; exact hq.mpr (h (hp.mp hf))
  | box p _ => rfl
  | diamond p _ => rfl

theorem duplicate_language_collapse :
    MC duplicates.frame (expressible duplicates.frame duplicates.valuation) false := by
  rintro P ⟨p, rfl⟩ hp v _
  cases v with
  | false => exact hp
  | true => exact duplicates_constant p |>.mp hp

theorem duplicate_identity_inadmissible :
    ¬ IdentityAdmissible (expressible duplicates.frame duplicates.valuation) false := by
  rintro ⟨p, he⟩
  have h := duplicates_constant p
  have hf : Holds duplicates.frame duplicates.valuation false p :=
    (congrFun he false).mp rfl
  have ht : (true : Bool) = false := (congrFun he true).mpr (h.mp hf)
  exact Bool.noConfusion ht

theorem duplicate_not_extensional :
    ¬ PropositionalExtensionality (expressible duplicates.frame duplicates.valuation) := by
  intro h
  have he := h false true (by rintro P ⟨p, rfl⟩; exact duplicates_constant p)
  exact Bool.noConfusion he

theorem branching_root_failure :
    eval branching false (.imp (.atom ()) (.box (.atom ()))) = false := rfl
theorem branching_terminal_success :
    eval branching true (.imp (.atom ()) (.box (.atom ()))) = true := rfl
theorem branching_witness : counterexamples branching false (.atom ()) = [true] := rfl
theorem branching_possibility : witnesses branching false (.atom ()) = [false] := rfl

/-- Scope (c) can omit a distinguishing sentence present in scope (b). -/
def inventory : Unit → Bool → Prop := fun _ _ => True

theorem inventory_collapse : MC branching.frame (corpusDomain inventory) false := by
  rintro P ⟨i, rfl⟩ _ v _
  trivial

theorem branching_language_not_collapse :
    ¬ MC branching.frame (expressible branching.frame branching.valuation) false := by
  intro h
  have ht := h (fun w => Holds branching.frame branching.valuation w (.atom ()))
    ⟨.atom (), rfl⟩ rfl true rfl
  change false = true at ht
  exact Bool.noConfusion ht

theorem branching_full_not_collapse : ¬ MC branching.frame allPredicates false := by
  intro h
  have he := identity_separates branching.frame allPredicates false trivial h true rfl
  exact Bool.noConfusion he

/-- Executable domain-relative MC over a supplied finite predicate inventory.
It makes no claim to enumerate all Prop-valued functions. -/
def collapseEval {W A : Type} (m : Model W A) (ps : List (W → Bool)) (w : W) : Bool :=
  ps.all (fun p => !p w || m.worlds.all (fun v => !m.edge w v || p v))

/-- A reproducible report exposes edges, truth-at-each-world, root evaluations,
accessible witnesses, and counterexample worlds. It never changes the root implicitly. -/
def report : String :=
  let p : Formula Unit := .atom ()
  let rows := branching.worlds.map (fun w =>
    (w, branching.worlds.map (fun v => (v, branching.edge w v)),
      eval branching w p, eval branching w (.box p), eval branching w (.diamond p),
      eval branching w (.imp p (.box p)), witnesses branching w p,
      counterexamples branching w p))
  reprStr rows

#guard eval deadEnd () (.box (.atom ())) == true
#guard eval deadEnd () (.diamond (.atom ())) == false
#guard witnesses deadEnd () (.atom ()) == []
#guard counterexamples deadEnd () (.atom ()) == []

#guard eval branching false (.atom ()) == true
#guard eval branching true (.atom ()) == false
#guard eval branching false (.box (.atom ())) == false
#guard eval branching true (.box (.atom ())) == false
#guard eval branching false (.diamond (.atom ())) == true
#guard eval branching true (.diamond (.atom ())) == false
#guard collapseEval branching [fun _ => true] false == true
#guard collapseEval branching [fun w => !w] false == false
#guard collapseEval branching [fun w => !w] true == true

/-- Exact fixture contract. No source or metaphysical premise is imported as a fact. -/
def Checks : Prop :=
  ResearchFixture.Checks ∧
  (∀ (W A : Type) (m : Model W A) (p : Formula A) w,
    eval m w p = true ↔ Holds m.frame m.valuation w p) ∧
  MC duplicates.frame (expressible duplicates.frame duplicates.valuation) false ∧
  (¬ IdentityAdmissible (expressible duplicates.frame duplicates.valuation) false) ∧
  (¬ PropositionalExtensionality (expressible duplicates.frame duplicates.valuation)) ∧
  MC branching.frame (corpusDomain inventory) false ∧
  (¬ MC branching.frame (expressible branching.frame branching.valuation) false) ∧
  (¬ MC branching.frame allPredicates false) ∧
  eval branching false (.imp (.atom ()) (.box (.atom ()))) = false ∧
  eval branching true (.imp (.atom ()) (.box (.atom ()))) = true ∧
  counterexamples branching false (.atom ()) = [true] ∧
  witnesses branching false (.atom ()) = [false]

end TruthCore.Modal.ResearchFinite
