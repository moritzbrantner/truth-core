module

public import TruthCore.Epistemology.SleepingBeauty1401
public import TruthCore.Logic.EpistemicAccuracy

/-! Analyst continuation of #1401. A finite amnesia model tests unrestricted
reflection; an accuracy comparison tests different populations of assessments.
Neither conditional probability nor an accuracy objective is a rationality
norm by definition. No theorem below licenses the population choice. -/

@[expose] public section
namespace TruthCore.Epistemology.SleepingBeauty1401.Reflection
open TruthCore.Epistemology.SleepingBeauty1401

/-- Fair two-world coin, conditional on an explicit report. A positive report
probability is checked in the concrete controls; empty events use field division. -/
def coinPosterior {Report : Type} [DecidableEq Report]
    (observe : World → Report) (report : Report) : ℚ :=
  (if observe .heads = report then 1/2 else 0) /
    ((if observe .heads = report then 1/2 else 0) +
     (if observe .tails = report then 1/2 else 0))

/-- Information retention means every old report is reconstructible from the
new report. It is a structural no-loss property, not a deference obligation. -/
def Retains {State Old New : Type} (before : State → Old) (after : State → New) : Prop :=
  ∃ reconstruct : New → Old, ∀ w, reconstruct (after w) = before w

def revealed (w : World) : World := w
def erased (_ : World) : Unit := ()
def beforeCredence (w : World) : ℚ := coinPosterior revealed (revealed w)
def afterCredence (w : World) : ℚ := coinPosterior erased (erased w)

/-- The first two statements show both credences really are the conditional
probabilities of the SAME fair coin on the agent's respective reports.
Conditioning now on both current knowledge and the known future report still
leaves current Heads certainty 1 (or Tails certainty 0), not future 1/2.
All conditioning events used have probability 1 or 1/2. -/
def AmnesiaControl : Prop :=
  beforeCredence .heads = 1 ∧ beforeCredence .tails = 0 ∧
  (∀ w, afterCredence w = 1/2) ∧
  (∀ w, coinPosterior (fun v => (revealed v, afterCredence v))
      (revealed w, (1/2:ℚ)) = beforeCredence w) ∧
  coinPosterior (fun _ : World => (1/2:ℚ)) (1/2:ℚ) = 1/2 ∧
  ¬ Retains revealed erased ∧ Retains erased revealed

/-- A fair coin paired with an independent fair private bit. The four atoms
have mass 1/4. The private bit is known and then erased, while the target is
still the coin. Thus structural information loss need not affect this target. -/
def pairPosterior {Report : Type} [DecidableEq Report]
    (observe : World × Bool → Report) (report : Report) : ℚ :=
  ((if observe (.heads, false) = report then 1/4 else 0) +
   (if observe (.heads, true) = report then 1/4 else 0)) /
  ((if observe (.heads, false) = report then 1/4 else 0) +
   (if observe (.heads, true) = report then 1/4 else 0) +
   (if observe (.tails, false) = report then 1/4 else 0) +
   (if observe (.tails, true) = report then 1/4 else 0))

def IrrelevantLossControl : Prop :=
  (∀ b : Bool, pairPosterior Prod.snd b = 1/2) ∧
  pairPosterior (fun _ : World × Bool => ()) () = 1/2 ∧
  ¬ Retains (Prod.snd : World × Bool → Bool) (fun _ => ())

/-- Each coin experiment has one designated first-Monday assessment. There is
no report variation in either Heads or Tails when an amnesiac agent follows a
constant fair-protocol rule r. The monitor's conditional Heads probability on
that report stays 1/2. No claim that the monitor's evidence equals Beauty's. -/
def FirstMondayCalibration : Prop :=
  (∀ r : ℚ, coinPosterior (fun _ : World => r) r = 1/2) ∧
  coinPosterior (fun _ : World => (1/3:ℚ)) (1/3:ℚ) ≠ 1/3 ∧
  Retains (fun _ : World => ()) (fun _ : World => ())

/-- Binary squared epistemic error, reusing the existing accuracy vocabulary.
The fair coin weights one H assessment and one T assessment per first-Monday
cohort. An all-token cohort instead includes one H and TWO T assessments;
its prospective sum below is not normalized by the number of awakenings.
The positive factor 3/2 does not affect its minimizer. -/
noncomputable def mondayRisk (r : ℝ) : ℝ :=
  TruthCore.Logic.EpistemicAccuracy.error (1/2) r
noncomputable def tokenRisk (r : ℝ) : ℝ := (1/2)*(1-r)^2 + r^2

/-- Unlike a ticket price, these are epistemic squared-error costs. No monetary
reward enters. The two minimizers conflict because they aggregate different
cohorts; neither r=1/2 nor r=1/3 statewise dominates the other. -/
def CohortAccuracy : Prop :=
  (∀ r : ℝ, mondayRisk r - mondayRisk (1/2) = (r-1/2)^2) ∧
  (∀ r : ℝ, tokenRisk r - tokenRisk (1/3) = (3/2)*(r-1/3)^2) ∧
  (∀ r : ℝ, (∀ s, mondayRisk r ≤ mondayRisk s) ↔ r=1/2) ∧
  (∀ r : ℝ, (∀ s, tokenRisk r ≤ tokenRisk s) ↔ r=1/3) ∧
  (¬ ∃ r : ℝ, (∀ s, mondayRisk r ≤ mondayRisk s) ∧
    (∀ s, tokenRisk r ≤ tokenRisk s)) ∧
  mondayRisk (1/3) - mondayRisk (1/2) = 1/36 ∧
  tokenRisk (1/2) - tokenRisk (1/3) = 1/24 ∧
  (1-(1/2:ℝ))^2 < (1-1/3)^2 ∧ (1/3:ℝ)^2 < (1/2)^2

/-- With reliable day information retained, Monday's forecast is 1/2 and
Tuesday's is 0. They jointly minimize total token score among day-sensitive
policies; forgetting the day forces one common r. The advantage of retaining
the day is strict at the best constant r=1/3. This is an accuracy comparison
under the token objective, not a proof that this objective is obligatory. -/
noncomputable def dayRisk (mon tue : ℝ) : ℝ :=
  (1/2)*(1-mon)^2 + (1/2)*mon^2 + (1/2)*tue^2

def RecallControl : Prop :=
  (∀ mon tue : ℝ, dayRisk mon tue - dayRisk (1/2) 0 =
    (mon-1/2)^2 + (1/2)*tue^2) ∧
  dayRisk (1/2) 0 = 1/4 ∧ tokenRisk (1/3) = 1/3 ∧
  (∀ r : ℝ, dayRisk r r = tokenRisk r) ∧
  dayRisk (1/2) 0 < tokenRisk (1/3)

end TruthCore.Epistemology.SleepingBeauty1401.Reflection
