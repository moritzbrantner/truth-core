import TruthCore.Explanation.UltimateAdequacy

/-! Analyst semantics for #744, not a source-derived account of cooperation.
Reuses the #733 `Exercise` records and #734 `Supply` unchanged. Every label below
is relative to one supplied scenario space and one supplied event carrier:
"brute" means only what `BruteCoincidence` says, not unexplained simpliciter.
`NecessaryIn` is occurrence at every allowed scenario; it is not modal necessity
until `ScenariosAreWorlds` or `WorldsAreScenarios` is supplied as a separate bridge.
Scenario sufficiency has no causal direction, so `CommonSource` also requires
exercised ancestry. See docs/notes/joint-cooperation-744.md. -/
namespace TruthCore.Explanation.JointCooperation
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic.Regress
open TruthCore.German.Kant.CosmologicalInference

variable {B E G S : Type}

/-- Both occur in the actual scenario. Nothing about any group. -/
def Coexist (m : Exercise B E G S) (a b : E) : Prop :=
  m.occurs m.actual a ∧ m.occurs m.actual b

/-- Both occur in some allowed scenario, possibly not the actual one. -/
def Compatible (m : Exercise B E G S) (a b : E) : Prop :=
  ∃ s, m.allowed s ∧ m.occurs s a ∧ m.occurs s b

/-- Actual coordination: two distinct contributors of one exercised group in a
coherent exercise. No sufficiency of the group is included. -/
def Coordinated (m : Exercise B E G S) (g : G) (a b : E) : Prop :=
  m.coherent ∧ m.exercised g ∧ a ∈ m.groups.contributors g ∧
    b ∈ m.groups.contributors g ∧ a ≠ b

/-- Occurrence at every allowed scenario of this exercise. -/
def NecessaryIn (m : Exercise B E G S) (e : E) : Prop :=
  ∀ s, m.allowed s → m.occurs s e

/-- The pair never comes apart in this scenario space. This records covariation;
it does not say what, if anything, accounts for it. -/
def MutualFit (m : Exercise B E G S) (a b : E) : Prop :=
  ∀ s, m.allowed s → (m.occurs s a ↔ m.occurs s b)

/-- With the rest of the group retained, one of the two can be deleted without
an allowed failure of the effect. -/
def NoCooperationNeeded (m : Exercise B E G S) (g : G) (a b : E) : Prop :=
  m.redundant g a ∨ m.redundant g b

def Needed (m : Exercise B E G S) (g : G) (a b : E) : Prop :=
  m.indispensable g a ∧ m.indispensable g b

/-- A single occurring event that is an exercised strict ancestor of both and
scenario-suffices for each. Neither ancestry nor sufficiency alone is enough. -/
def CommonSource (m : Exercise B E G S) (a b : E) : Prop :=
  ∃ c, m.occurs m.actual c ∧
    ancestry m.exercisedGroups.graph c a ∧ ancestry m.exercisedGroups.graph c b ∧
    m.suffices {c} a ∧ m.suffices {c} b

/-- They coexist, they come apart in an allowed scenario, and no event of this
carrier is a common source. Relative to this scenario space and carrier. -/
def BruteCoincidence (m : Exercise B E G S) (a b : E) : Prop :=
  Coexist m a b ∧ ¬ MutualFit m a b ∧ ¬ CommonSource m a b

/-- Each contributor occurs at an allowed scenario without the other and without
the effect. -/
def TwoWayVariation (m : Exercise B E G S) (g : G) (a b : E) : Prop :=
  (∃ s, m.allowed s ∧ m.occurs s b ∧ ¬ m.occurs s a ∧ ¬ m.occurs s (m.groups.effect g)) ∧
  (∃ s, m.allowed s ∧ m.occurs s a ∧ ¬ m.occurs s b ∧ ¬ m.occurs s (m.groups.effect g))

/-- Every allowed scenario has exactly the occurrence table of an accessible world. -/
def ScenariosAreWorlds {W : Type} (m : Exercise B E G S) (o : Ontic W E) (w : W) : Prop :=
  ∀ s, m.allowed s → ∃ v, o.frame.access w v ∧ ∀ e, m.occurs s e ↔ o.ExistsAt v e

/-- Every accessible world has exactly the occurrence table of an allowed scenario. -/
def WorldsAreScenarios {W : Type} (m : Exercise B E G S) (o : Ontic W E) (w : W) : Prop :=
  ∀ v, o.frame.access w v → ∃ s, m.allowed s ∧ ∀ e, m.occurs s e ↔ o.ExistsAt v e

/-- Coverage for one coordinated, jointly sufficient pair, in the four-way form
and in the sharper form. Branches overlap; exclusivity is not claimed. -/
def Coverage : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S) (g : G) (a b : E),
    Coordinated m g a b → m.jointlySufficient g →
    (NoCooperationNeeded m g a b ∨ CommonSource m a b ∨ MutualFit m a b ∨
      BruteCoincidence m a b) ∧
    (NoCooperationNeeded m g a b ∨
      (TwoWayVariation m g a b ∧ (CommonSource m a b ∨ BruteCoincidence m a b)))

/-- What each branch brings with it. The first block assumes one coordinated,
jointly sufficient pair; the last four clauses assume neither. -/
def BranchCosts : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S) (g : G) (a b : E),
    (Coordinated m g a b → m.jointlySufficient g →
      -- mutual fit makes both contributors redundant
      (MutualFit m a b → m.redundant g a ∧ m.redundant g b) ∧
      -- needing both forces two-way variation and refutes occurrence everywhere
      (Needed m g a b → TwoWayVariation m g a b ∧ ¬ MutualFit m a b ∧
        ¬ NecessaryIn m a ∧ ¬ NecessaryIn m b) ∧
      -- a contributor occurring at every allowed scenario is redundant
      (NecessaryIn m a → m.redundant g a) ∧
      -- members occurring everywhere: so does the effect
      ((∀ e ∈ m.groups.members g, NecessaryIn m e) → NecessaryIn m (m.groups.effect g)) ∧
      -- an event sufficing for each member suffices for the effect
      (∀ c, (∀ e ∈ m.groups.members g, m.suffices {c} e) →
        m.suffices {c} (m.groups.effect g)) ∧
      -- an event mutually sufficient with each contributor gives fit
      (∀ c, m.suffices {c} a → m.suffices {c} b → m.suffices {a} c → m.suffices {b} c →
        MutualFit m a b) ∧
      -- with both needed, each contributor occurs at a scenario without the determiner
      (∀ c, Needed m g a b → m.suffices {c} a → m.suffices {c} b →
        (∃ s, m.allowed s ∧ m.occurs s a ∧ ¬ m.occurs s c) ∧
        (∃ s, m.allowed s ∧ m.occurs s b ∧ ¬ m.occurs s c)) ∧
      -- an everywhere-occurring determiner of a contributor excludes needing both
      (∀ c, NecessaryIn m c → m.suffices {c} a → ¬ Needed m g a b)) ∧
    -- two contributors occurring everywhere fit
    (NecessaryIn m a → NecessaryIn m b → MutualFit m a b) ∧
    -- no common source when either is an exercised source
    (m.exercisedGroups.graph.Source a → ¬ CommonSource m a b) ∧
    (m.exercisedGroups.graph.Source b → ¬ CommonSource m a b) ∧
    -- scenario sufficiency of an everywhere-occurring effect is uninformative
    (NecessaryIn m a ↔ m.suffices ∅ a)

/-- Excluding the fit branch among contributors occurring everywhere says exactly
that the group has at most one such contributor. A per-group statement. -/
def FitExclusionIsAtMostOne : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S) (g : G),
    (∀ a b, a ∈ m.groups.contributors g → NecessaryIn m a →
      b ∈ m.groups.contributors g → NecessaryIn m b → a ≠ b → ¬ MutualFit m a b) ↔
    (∀ a b, a ∈ m.groups.contributors g → NecessaryIn m a →
      b ∈ m.groups.contributors g → NecessaryIn m b → a = b)

/-- These four force the pair into the brute branch, so adding its denial is an
incompatible core. One contributor is an exercised source; the other need not be.
No count of sources occurs. -/
def IncompatibleCore : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S) (g : G) (a b : E),
    Coordinated m g a b → m.jointlySufficient g → m.exercisedGroups.graph.Source a →
    Needed m g a b → BruteCoincidence m a b

/-- The modal bridges, each explicit. -/
def ModalBridges : Prop :=
  ∀ (B E G S W : Type) (m : Exercise B E G S) (o : Ontic W E) (w : W),
    (ScenariosAreWorlds m o w → ∀ e, NecessaryAt o w e → NecessaryIn m e) ∧
    (WorldsAreScenarios m o w → ∀ e, NecessaryIn m e → NecessaryAt o w e) ∧
    (∀ (g : G) (a b : E), Coordinated m g a b → m.jointlySufficient g →
      Needed m g a b → NecessaryAt o w a → ¬ ScenariosAreWorlds m o w)

abbrev exercisePlural := UltimateAdequacy.exercise .plural

/-- The #735 plural fixture with unchanged events, records, occurrence table and
actual scenario, restricted to the actual scenario. -/
def narrow : Exercise Nat Nat Nat (Bool × Bool) :=
  { exercisePlural with allowed := fun s => s = (true, true) }

/-- The #735 plural fixture off the actual scenario and with no exercised record:
same scenario space, same sufficiency and indispensability. -/
def apart : Exercise Nat Nat Nat (Bool × Bool) :=
  { exercisePlural with actual := (true, false), exercised := fun _ => False }

inductive FitEvent | l | r | t | e deriving DecidableEq
inductive FitGroup | joint | free deriving DecidableEq

def fitGroups : Groups FitEvent FitGroup where
  contributors := fun g => {x | match g with
    | .joint => x = .l ∨ x = .r
    | .free => x = .t}
  enablers := fun _ => ∅
  effect := fun g => match g with | .joint => .t | .free => .e
  admitted := fun _ => True

def fitIntrinsic (x : FitEvent) : Prop := x = .l ∨ x = .r

/-- Two contributors and their effect occur at every scenario; a further effect
`e` is contingent, through a record that is exercised and not sufficient. -/
def fit : Exercise Unit FitEvent FitGroup Bool where
  groups := fitGroups
  bearer := fun _ => ()
  occurs := fun s x => match x with
    | .l | .r | .t => True
    | .e => s = true
  allowed := fun _ => True
  actual := true
  exercised := fun _ => True

/-- As `fit`, except that the joint effect `t` varies freely, so the group is
exercised and not sufficient. -/
def loose : Exercise Unit FitEvent FitGroup Bool :=
  { fit with occurs := fun s x => match x with
    | .l | .r => True
    | .t | .e => s = true }

inductive SingleEvent | r | a | b | t deriving DecidableEq
inductive SingleGroup | ra | rb | ab deriving DecidableEq

def singleGroups : Groups SingleEvent SingleGroup where
  contributors := fun g => {x | match g with
    | .ra | .rb => x = .r
    | .ab => x = .a ∨ x = .b}
  enablers := fun _ => ∅
  effect := fun g => match g with | .ra => .a | .rb => .b | .ab => .t
  admitted := fun _ => True

def singleIntrinsic (x : SingleEvent) : Prop := x = .r

/-- One source occurring at every scenario; it is an ancestor of both contributors
but its records are not sufficient for them. -/
def single : Exercise Unit SingleEvent SingleGroup (Bool × Bool) where
  groups := singleGroups
  bearer := fun _ => ()
  occurs := fun s x => match x with
    | .r => True
    | .a => s.1 = true
    | .b => s.2 = true
    | .t => s.1 = true ∧ s.2 = true
  allowed := fun _ => True
  actual := (true, true)
  exercised := fun _ => True

inductive GuidedEvent | l | r | d | x | y | a | b | t deriving DecidableEq
inductive GuidedGroup | lr | ld | lx | ry | da | xa | db | yb | ab deriving DecidableEq

/-- `two = true`: record `lr` is not admitted, so `r` is a second source.
`two = false`: `lr` is admitted and `l` is the only source. Occurrence is the same. -/
def guidedGroups (two : Bool) : Groups GuidedEvent GuidedGroup where
  contributors := fun g => {e | match g with
    | .lr | .ld | .lx => e = .l
    | .ry => e = .r
    | .da | .db => e = .d
    | .xa => e = .x
    | .yb => e = .y
    | .ab => e = .a ∨ e = .b}
  enablers := fun _ => ∅
  effect := fun g => match g with
    | .lr => .r | .ld => .d | .lx => .x | .ry => .y
    | .da | .xa => .a
    | .db | .yb => .b
    | .ab => .t
  admitted := fun g => g = .lr → two = false

def guidedIntrinsic (two : Bool) (e : GuidedEvent) : Prop :=
  e = .l ∨ (two = true ∧ e = .r)

/-- `a` and `b` have the common determiner `d` and also separate routes `x`, `y`,
so each is indispensable for `t` while `d` is not needed for either. The three
bits vary freely; `l` and `r` occur at every scenario. -/
def guided (two : Bool) : Exercise Unit GuidedEvent GuidedGroup (Bool × Bool × Bool) where
  groups := guidedGroups two
  bearer := fun _ => ()
  occurs := fun s e => match e with
    | .l | .r => True
    | .d => s.1 = true
    | .x => s.2.1 = true
    | .y => s.2.2 = true
    | .a => s.1 = true ∨ s.2.1 = true
    | .b => s.1 = true ∨ s.2.2 = true
    | .t => (s.1 = true ∨ s.2.1 = true) ∧ (s.1 = true ∨ s.2.2 = true)
  allowed := fun _ => True
  actual := (true, true, true)
  exercised := fun g => (guidedGroups two).admitted g

/-- Coexistence, compatibility, coordination, sufficiency and Supply come apart. -/
def Ladder : Prop :=
  (Coexist fit .l .r ∧
    ¬ Coordinated { fit with exercised := fun _ => False } .joint .l .r) ∧
  (Compatible apart 0 1 ∧ ¬ Coexist apart 0 1) ∧
  (Coordinated loose .joint .l .r ∧ ¬ loose.jointlySufficient .joint) ∧
  (Coordinated (UltimateAdequacy.exercise .branch) 1 0 3 ∧
    (UltimateAdequacy.exercise .branch).jointlySufficient 1 ∧
    ¬ Supply (UltimateAdequacy.groups .branch) (UltimateAdequacy.intrinsic .branch) 2)

/-- `fit` read modally: worlds are its scenarios; causes are exercised edges between
events existing at that world. A stipulated overlay, not a possibility claim. -/
def fitOntic : Ontic Bool FitEvent where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fit.occurs
  Causes := fun w y x => fit.occurs w y ∧ fit.occurs w x ∧ fit.exercisedGroups.graph.edge y x

/-- A plural rival in the same-space fit branch: two distinct exercised sources,
Supply of every event, no least event, the effect `t` occurring everywhere, both
contributors redundant, and a contingent event `e`. With scenarios and worlds
matching, the sources and `t` are necessary at `true` and `e` is contingent there. -/
def FitRival : Prop :=
  Coordinated fit .joint .l .r ∧ fit.jointlySufficient .joint ∧
  MutualFit fit .l .r ∧ fit.redundant .joint .l ∧ fit.redundant .joint .r ∧
  NecessaryIn fit .l ∧ NecessaryIn fit .r ∧ NecessaryIn fit .t ∧
  ¬ BruteCoincidence fit .l .r ∧ ¬ CommonSource fit .l .r ∧
  ¬ NecessaryIn fit .e ∧ fit.exercised .free ∧ ¬ fit.jointlySufficient .free ∧
  fit.exercisedGroups.graph.Source .l ∧ fit.exercisedGroups.graph.Source .r ∧
  (∀ x, Supply fit.groups fitIntrinsic x) ∧
  (¬ ∃ s, least fit.exercisedGroups.graph s) ∧
  fit.suffices ∅ .t ∧
  ScenariosAreWorlds fit fitOntic true ∧ WorldsAreScenarios fit fitOntic true ∧
  NecessaryAt fitOntic true .l ∧ NecessaryAt fitOntic true .r ∧ NecessaryAt fitOntic true .t ∧
  ContingentAt fitOntic true .e ∧
  (∀ y x, fitOntic.Causes true y x ↔ fit.exercisedGroups.graph.edge y x)

/-- A plural rival in the variation branch: the #735 fixture. Both needed, brute by
the definition above, Supply of every event, no least event. Both #735 overlays
make its contributors necessary at the designated world, and for neither overlay
is every scenario a world. The same records, restricted to the actual scenario,
land in the fit branch, with scenarios and worlds matching for the all-necessary
overlay. -/
def VariationRival : Prop :=
  Coordinated exercisePlural 0 0 1 ∧ exercisePlural.jointlySufficient 0 ∧
  Needed exercisePlural 0 0 1 ∧ BruteCoincidence exercisePlural 0 1 ∧
  exercisePlural.exercisedGroups.graph.Source 0 ∧
  exercisePlural.exercisedGroups.graph.Source 1 ∧
  (∀ e, Supply exercisePlural.groups (UltimateAdequacy.intrinsic .plural) e) ∧
  (¬ ∃ s, least exercisePlural.exercisedGroups.graph s) ∧
  (∀ b, NecessaryAt (UltimateAdequacy.modal .plural b) false 0 ∧
    NecessaryAt (UltimateAdequacy.modal .plural b) false 1 ∧
    ¬ ScenariosAreWorlds exercisePlural (UltimateAdequacy.modal .plural b) false) ∧
  (Coordinated narrow 0 0 1 ∧ narrow.jointlySufficient 0 ∧ MutualFit narrow 0 1 ∧
    narrow.redundant 0 0 ∧ narrow.redundant 0 1 ∧
    NecessaryIn narrow 0 ∧ NecessaryIn narrow 1 ∧ NecessaryIn narrow 2 ∧
    ¬ BruteCoincidence narrow 0 1 ∧
    ScenariosAreWorlds narrow (UltimateAdequacy.modal .plural true) false ∧
    WorldsAreScenarios narrow (UltimateAdequacy.modal .plural true) false)

/-- A single source does not remove the brute branch: one least event, the only
exercised source, occurs everywhere; both contributors are needed and the pair is
brute by the definition above. -/
def SingleSourceBrute : Prop :=
  Coordinated single .ab .a .b ∧ single.jointlySufficient .ab ∧
  Needed single .ab .a .b ∧ BruteCoincidence single .a .b ∧
  least single.exercisedGroups.graph .r ∧ single.exercisedGroups.graph.Source .r ∧
  (∀ x, single.exercisedGroups.graph.Source x → x = .r) ∧
  NecessaryIn single .r ∧
  (∀ x, Supply single.groups singleIntrinsic x)

/-- Source count does not decide this branch: at both settings of `two`, the pair
`a`, `b` has a common source and both are needed, and no coordinated pair is brute.
One setting has two distinct sources and no least event; the other has `l` as least
event and only source. -/
def GuidedParity : Prop :=
  (∀ two, Coordinated (guided two) .ab .a .b ∧ (guided two).jointlySufficient .ab ∧
    Needed (guided two) .ab .a .b ∧ CommonSource (guided two) .a .b ∧
    (∀ g p q, Coordinated (guided two) g p q → ¬ BruteCoincidence (guided two) p q) ∧
    NecessaryIn (guided two) .l ∧ NecessaryIn (guided two) .r ∧
    (∀ e, Supply (guided two).groups (guidedIntrinsic two) e)) ∧
  ((guided true).exercisedGroups.graph.Source .l ∧
    (guided true).exercisedGroups.graph.Source .r ∧
    ¬ ∃ s, least (guided true).exercisedGroups.graph s) ∧
  (least (guided false).exercisedGroups.graph .l ∧
    (guided false).exercisedGroups.graph.Source .l ∧
    ∀ z, (guided false).exercisedGroups.graph.Source z → z = .l)

/-- ST I q.11 a.3 co., third proof, "Quae autem diversa sunt, in unum ordinem non
convenirent, nisi ab aliquo uno ordinarentur", read pairwise and weakly: distinct
contributors of one exercised record have one exercised ancestor. Coming together
in one order is read as joint contribution to one effect, and being ordered by one
as ancestry only, without sufficiency. Both are analyst readings. The source's
`deserviunt`, "per se unius unum est causa" and "perfectissimum" are not encoded. -/
def PairwiseOrderer (m : Exercise B E G S) : Prop :=
  ∀ g a b, Coordinated m g a b →
    ∃ c, ancestry m.exercisedGroups.graph c a ∧ ancestry m.exercisedGroups.graph c b

/-- The same passage, with "Omnia enim quae sunt" and "primum reducens omnia in
unum ordinem", read totally: one event has a finite exercised path to every event. -/
def TotalOrderer (m : Exercise B E G S) : Prop :=
  ∃ c, least m.exercisedGroups.graph c

/-- The pairwise reading excludes a source as a coordinated contributor. It
holds with two sources and no total orderer. The total reading gives at most one
exercised source outright, so it is not independent of that conclusion. Holding
the pairwise reading does not remove the brute branch as defined above. -/
def OrderReadings : Prop :=
  (∀ (B E G S : Type) (m : Exercise B E G S), PairwiseOrderer m →
    ∀ g a b, Coordinated m g a b → ¬ m.exercisedGroups.graph.Source a) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S), TotalOrderer m →
    ∀ x y, m.exercisedGroups.graph.Source x → m.exercisedGroups.graph.Source y → x = y) ∧
  (PairwiseOrderer (guided true) ∧ ¬ TotalOrderer (guided true) ∧
    (guided true).exercisedGroups.graph.Source .l ∧
    (guided true).exercisedGroups.graph.Source .r) ∧
  (PairwiseOrderer single ∧ TotalOrderer single ∧ BruteCoincidence single .a .b) ∧
  ¬ PairwiseOrderer fit ∧ ¬ PairwiseOrderer exercisePlural

/-- Each of the five members of the core can be omitted with the other four held. -/
def CoreDeletions : Prop :=
  -- coordination omitted
  (¬ Coordinated apart 0 0 1 ∧ apart.jointlySufficient 0 ∧
    apart.exercisedGroups.graph.Source 0 ∧ Needed apart 0 0 1 ∧
    ¬ BruteCoincidence apart 0 1) ∧
  -- sufficiency omitted
  (Coordinated loose .joint .l .r ∧ ¬ loose.jointlySufficient .joint ∧
    loose.exercisedGroups.graph.Source .l ∧ Needed loose .joint .l .r ∧
    ¬ BruteCoincidence loose .l .r) ∧
  -- source omitted
  (Coordinated (guided false) .ab .a .b ∧ (guided false).jointlySufficient .ab ∧
    ¬ (guided false).exercisedGroups.graph.Source .a ∧
    Needed (guided false) .ab .a .b ∧ ¬ BruteCoincidence (guided false) .a .b) ∧
  -- both-needed omitted
  (Coordinated fit .joint .l .r ∧ fit.jointlySufficient .joint ∧
    fit.exercisedGroups.graph.Source .l ∧ ¬ Needed fit .joint .l .r ∧
    ¬ BruteCoincidence fit .l .r) ∧
  -- no-brute omitted
  (Coordinated exercisePlural 0 0 1 ∧ exercisePlural.jointlySufficient 0 ∧
    exercisePlural.exercisedGroups.graph.Source 0 ∧ Needed exercisePlural 0 0 1 ∧
    BruteCoincidence exercisePlural 0 1)

def Certificate : Prop :=
  Coverage ∧ BranchCosts ∧ FitExclusionIsAtMostOne ∧ IncompatibleCore ∧ ModalBridges ∧
  Ladder ∧ FitRival ∧ VariationRival ∧ SingleSourceBrute ∧ GuidedParity ∧ CoreDeletions ∧
  OrderReadings ∧ PluralMinima ∧ UltimateAdequacy.Structural

end TruthCore.Explanation.JointCooperation
