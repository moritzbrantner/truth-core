module

public import TruthCore.Spacetime.BoostSimultaneity

/-! Analyst protocol candidate, attribution deferred. Arbitrary event, clock and
location domains; real chart parameters are framework inputs, not a physical
spacetime theorem. Signals and clock trajectories are independently supplied. -/
@[expose] public section
namespace TruthCore.Spacetime.StationaryClockProtocol
noncomputable section

structure System (Event Clock Location : Type) where
  eventParameter : Event → ℝ
  eventLocation : Event → Location
  position : Clock → ℝ → Location
  readout : Clock → ℝ → ℝ
  reference : Clock
  /-- Emission at a, reflection at b, reception at d; first and last
  occur at the first clock, reflection at the second. Light propagation
  is a primitive input, not inferred from three ordered timestamps. -/
  lightExchange : Clock → Clock → ℝ → ℝ → ℝ → Prop

def Stationary (s : System E C L) : Prop :=
  ∀ c t u, s.position c t = s.position c u

def At (s : System E C L) (c : C) (e : E) : Prop :=
  s.position c (s.eventParameter e) = s.eventLocation e

/-- The local instrument indication, before any remote synchronization. -/
def localTime (s : System E C L) (c : C) (e : E) : ℝ :=
  s.readout c (s.eventParameter e)

def Midpoint (s : System E C L) (r c : C) : Prop :=
  ∀ a b d, s.lightExchange r c a b d →
    s.readout c b = (s.readout r a + s.readout r d) / 2

/-- Nonvacuous coverage at every chart parameter for every pair of clocks.
Ordered send/reflection/return is required independently of calibration. -/
def Coverage (s : System E C L) : Prop :=
  ∀ r c b, ∃ a d, a < b ∧ b < d ∧ s.lightExchange r c a b d

/-- Conditional stationary-system profile. A common positive rate relative to
this chart, and a common origin, are explicit calibration assumptions. They
are stronger than one isolated midpoint test; no dynamics is derived. -/
structure Calibrated (s : System E C L) : Prop where
  stationary : Stationary s
  coverage : Coverage s
  midpoint : ∀ c, Midpoint s s.reference c
  commonCalibration : ∃ rate origin : ℝ, 0 < rate ∧
    ∀ c t, s.readout c t = rate * t + origin

/-- Event time is a *local* indication with instrument-at-event evidence.
The profile supplies synchronized stationary coverage, not ontic presence. -/
def Timestamp (s : System E C L) (e : E) (t : ℝ) : Prop :=
  Calibrated s ∧ ∃ c, At s c e ∧ localTime s c e = t

/-- Any two clocks give the same reading at an event's chart parameter. This
follows from `Calibrated.commonCalibration` alone: stationarity, coverage and
midpoint agreement are not used, and no `At` hypothesis is assumed, so it is
NOT a statement about instruments present at the event. -/
theorem calibrated_localTime_eq (s : System E C L) (h : Calibrated s)
    (c d : C) (e : E) : localTime s c e = localTime s d e := by
  obtain ⟨rate, origin, _, hc⟩ := h.commonCalibration
  simp only [localTime, hc]

/-- Under the profile, all clocks have equal readouts at every chart parameter
(equality, hence trivially symmetric and transitive). Only
`Calibrated.commonCalibration` is used; midpoint and coverage are not used and
are not silently treated as rate calibration. -/
theorem calibrated_readout_eq (s : System E C L) (h : Calibrated s) (c d : C) (t : ℝ) :
    s.readout c t = s.readout d t := by
  obtain ⟨rate, origin, _, hc⟩ := h.commonCalibration
  rw [hc, hc]

/-- Changing the reference preserves the candidate only when the newly
selected reference satisfies midpoint calibration with every local clock. -/
theorem change_reference (s : System E C L) (h : Calibrated s) (r : C)
    (hr : ∀ c, Midpoint s r c) :
    Calibrated { s with reference := r } :=
  ⟨h.stationary, h.coverage, hr, h.commonCalibration⟩

/-- Dictionary to a selected history's real time labels. This is the exact
missing bridge input, not a theorem identifying physical clocks with history. -/
def HistoryDictionary (s : System E C L) (label : E → ℝ) : Prop :=
  ∀ e c, At s c e → label e = localTime s c e

theorem selected_order (s : System E C L) (label : E → ℝ)
    (hd : HistoryDictionary s label) (e f : E) (c d : C)
    (he : At s c e) (hf : At s d f) :
    label e < label f ↔ localTime s c e < localTime s d f := by
  rw [hd e c he, hd f d hf]

/-- Infinite-domain diagnostic family. All clocks are stationary at their
real location; exchanges have unit chart travel time. This abstract signal
family is not claimed to model distance-dependent physical propagation. -/
def offsetSystem (offset : ℝ → ℝ) (reference : ℝ) : System (ℝ × ℝ) ℝ ℝ where
  eventParameter := Prod.fst
  eventLocation := Prod.snd
  position c _ := c
  readout c t := t + offset c
  reference := reference
  lightExchange _ _ a b d := a = b - 1 ∧ d = b + 1

theorem offset_midpoint (o : ℝ → ℝ) (r c : ℝ) :
    Midpoint (offsetSystem o r) r c ↔ o c = o r := by
  constructor
  · intro h
    have hz := h (-1) 0 1 ⟨by norm_num, by norm_num⟩
    dsimp [offsetSystem] at hz
    linarith
  · intro h a b d ⟨ha, hd⟩
    dsimp [offsetSystem] at *
    rw [ha, hd, h]
    ring

theorem zero_calibrated : Calibrated (offsetSystem (fun _ => 0) 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c t u; rfl
  · intro r c b
    exact ⟨b - 1, b + 1, by linarith, by linarith, rfl, rfl⟩
  · intro c; exact (offset_midpoint _ _ _).2 rfl
  · exact ⟨1, 0, by norm_num, by intros; simp [offsetSystem]⟩

/-- Unsynchronized offsets defeat midpoint calibration; changing the reference
changes which offset is demanded. -/
theorem offset_failure : ¬ Midpoint (offsetSystem id 0) 0 1 := by
  rw [offset_midpoint]; norm_num

theorem remote_is_not_local :
    ¬ At (offsetSystem (fun _ => 0) 0) 1 (0, 0) := by
  norm_num [At, offsetSystem]

/-- Reference changes are conditional, not arbitrary conventions that
repair disagreeing instrument offsets. -/
theorem reference_control :
    Midpoint (offsetSystem id 1) 1 1 ∧
    ¬ Midpoint (offsetSystem id 1) 1 0 := by
  constructor
  · exact (offset_midpoint _ _ _).2 rfl
  · rw [offset_midpoint]; norm_num

/-- Unequal clock rates: clock c reads (c + 1) * t. -/
def rateSystem : System (ℝ × ℝ) ℝ ℝ :=
  { offsetSystem (fun _ => 0) 0 with readout := fun c t => (c + 1) * t }

/-- Rate mismatch passes the isolated exchange reflected at chart parameter 0
(emission -1, return 1), yet fails the midpoint protocol for the exchange
reflected at parameter 1 (emission 0, return 2). -/
theorem rate_failure :
    (rateSystem.lightExchange 0 1 (-1) 0 1 ∧
      rateSystem.readout 1 0 =
        (rateSystem.readout 0 (-1) + rateSystem.readout 0 1) / 2) ∧
    ¬ Midpoint rateSystem 0 1 := by
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num [rateSystem]⟩, ?_⟩
  intro h
  have hf := h 0 1 2 ⟨by norm_num, by norm_num⟩
  norm_num [rateSystem] at hf

/-- Empty exchanges do not satisfy coverage even if midpoint is vacuous. -/
theorem empty_exchange_failure :
    ¬ Coverage { offsetSystem (fun _ => 0) 0 with lightExchange := fun _ _ _ _ _ => False } := by
  intro h
  obtain ⟨a, d, _, _, hf⟩ := h 0 0 0
  exact hf

/-- Actual motion is rejected, rather than hidden behind a stationarity flag. -/
theorem moving_failure :
    ¬ Stationary { offsetSystem (fun _ => 0) 0 with position := fun c t => c + t } := by
  intro h
  have hf := h 0 0 1
  norm_num at hf

/-- Equal coordinate parameters alone do not imply equal instrument readings. -/
theorem equal_parameter_failure :
    BoostSimultaneity.Simultaneous (0, 0) (0, 1) ∧
    localTime (offsetSystem id 0) 0 (0, 0) ≠
      localTime (offsetSystem id 0) 1 (0, 1) := by
  constructor
  · rfl
  · norm_num [localTime, offsetSystem]
end
end TruthCore.Spacetime.StationaryClockProtocol
