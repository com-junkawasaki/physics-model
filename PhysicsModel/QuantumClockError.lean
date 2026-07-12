import PhysicsModel.ClockGauge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Concrete finite-accuracy quantum-clock noise

An imperfect clock record is modeled as a convex mixture of the ideal
conditional probability and a normalized backreaction/reference probability.
The mixture weight directly bounds the prediction error.
-/

namespace PhysicsModel.QuantumClockError

/-- Pointwise validity conditions for conditional probabilities. -/
structure ValidExperiment (experiment : ProbabilisticExperiment) : Prop where
  nonnegative : ∀ τ a, 0 ≤ experiment.probability τ a
  atMostOne : ∀ τ a, experiment.probability τ a ≤ 1

/-- Convex clock noise/backreaction channel. -/
noncomputable def noisyExperiment
    (ideal reference : ProbabilisticExperiment)
    (sameReading : ideal.ClockReading = reference.ClockReading)
    (sameOutcome : ideal.SystemOutcome = reference.SystemOutcome)
    (delta : ℝ) : ProbabilisticExperiment where
  ClockReading := ideal.ClockReading
  SystemOutcome := ideal.SystemOutcome
  probability := fun τ a =>
    (1 - delta) * ideal.probability τ a +
      delta * reference.probability (sameReading ▸ τ) (sameOutcome ▸ a)

theorem noisy_sub_ideal
    (ideal reference : ProbabilisticExperiment)
    (sameReading : ideal.ClockReading = reference.ClockReading)
    (sameOutcome : ideal.SystemOutcome = reference.SystemOutcome)
    (delta : ℝ) (τ : ideal.ClockReading) (a : ideal.SystemOutcome) :
    (noisyExperiment ideal reference sameReading sameOutcome delta).probability τ a -
        ideal.probability τ a =
      delta * (reference.probability (sameReading ▸ τ) (sameOutcome ▸ a) -
        ideal.probability τ a) := by
  unfold noisyExperiment
  dsimp
  ring

theorem probability_difference_le_one
    {ideal reference : ProbabilisticExperiment}
    (idealValid : ValidExperiment ideal) (referenceValid : ValidExperiment reference)
    (sameReading : ideal.ClockReading = reference.ClockReading)
    (sameOutcome : ideal.SystemOutcome = reference.SystemOutcome)
    (τ : ideal.ClockReading) (a : ideal.SystemOutcome) :
    |reference.probability (sameReading ▸ τ) (sameOutcome ▸ a) -
      ideal.probability τ a| ≤ 1 := by
  apply (abs_le).2
  constructor
  · linarith [referenceValid.nonnegative (sameReading ▸ τ) (sameOutcome ▸ a),
      idealValid.atMostOne τ a]
  · linarith [referenceValid.atMostOne (sameReading ▸ τ) (sameOutcome ▸ a),
      idealValid.nonnegative τ a]

/-- The backreaction mixture weight is a uniform operational clock-error bound. -/
theorem noisy_error_controlled
    {ideal reference : ProbabilisticExperiment}
    (idealValid : ValidExperiment ideal) (referenceValid : ValidExperiment reference)
    (sameReading : ideal.ClockReading = reference.ClockReading)
    (sameOutcome : ideal.SystemOutcome = reference.SystemOutcome)
    {delta : ℝ} (delta_nonnegative : 0 ≤ delta)
    (τ : ideal.ClockReading) (a : ideal.SystemOutcome) :
    |ideal.probability τ a -
      (noisyExperiment ideal reference sameReading sameOutcome delta).probability τ a| ≤ delta := by
  rw [abs_sub_comm]
  rw [noisy_sub_ideal]
  rw [abs_mul, abs_of_nonneg delta_nonnegative]
  have h := probability_difference_le_one idealValid referenceValid
    sameReading sameOutcome τ a
  simpa using mul_le_mul_of_nonneg_left h delta_nonnegative

/-- Convex clock noise preserves the probability interval `[0,1]`. -/
theorem noisy_valid
    {ideal reference : ProbabilisticExperiment}
    (idealValid : ValidExperiment ideal) (referenceValid : ValidExperiment reference)
    (sameReading : ideal.ClockReading = reference.ClockReading)
    (sameOutcome : ideal.SystemOutcome = reference.SystemOutcome)
    {delta : ℝ} (delta_nonnegative : 0 ≤ delta) (delta_atMostOne : delta ≤ 1) :
    ValidExperiment (noisyExperiment ideal reference sameReading sameOutcome delta) := by
  constructor
  · intro τ a
    unfold noisyExperiment
    dsimp
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr delta_atMostOne) (idealValid.nonnegative τ a))
      (mul_nonneg delta_nonnegative
        (referenceValid.nonnegative (sameReading ▸ τ) (sameOutcome ▸ a)))
  · intro τ a
    unfold noisyExperiment
    dsimp
    have hfirst := mul_le_mul_of_nonneg_left (idealValid.atMostOne τ a)
      (sub_nonneg.mpr delta_atMostOne)
    have hsecond := mul_le_mul_of_nonneg_left
      (referenceValid.atMostOne (sameReading ▸ τ) (sameOutcome ▸ a))
      delta_nonnegative
    linarith

/-- Concrete approximate clock change from an ideal clock to its noisy record. -/
noncomputable def approximateChange
    {ideal reference : ProbabilisticExperiment}
    (idealValid : ValidExperiment ideal) (referenceValid : ValidExperiment reference)
    (sameReading : ideal.ClockReading = reference.ClockReading)
    (sameOutcome : ideal.SystemOutcome = reference.SystemOutcome)
    (delta : ℝ) (delta_nonnegative : 0 ≤ delta) :
    ApproximateClockChange ideal
      (noisyExperiment ideal reference sameReading sameOutcome delta) where
  reading := id
  outcome := id
  error := delta
  error_nonnegative := delta_nonnegative
  controlled := noisy_error_controlled idealValid referenceValid sameReading sameOutcome
    delta_nonnegative

/-- With zero mixture weight the noisy clock is exactly the ideal clock. -/
theorem zero_noise_exact
    (ideal reference : ProbabilisticExperiment)
    (sameReading : ideal.ClockReading = reference.ClockReading)
    (sameOutcome : ideal.SystemOutcome = reference.SystemOutcome)
    (τ : ideal.ClockReading) (a : ideal.SystemOutcome) :
    (noisyExperiment ideal reference sameReading sameOutcome 0).probability τ a =
      ideal.probability τ a := by
  simp [noisyExperiment]

/-- Two successive concrete noisy clocks inherit the additive error bound. -/
theorem two_clock_error_bound
    {first second third : ProbabilisticExperiment}
    (firstChange : ApproximateClockChange first second)
    (secondChange : ApproximateClockChange second third)
    (τ : first.ClockReading) (a : first.SystemOutcome) :
    |first.probability τ a -
      third.probability
        ((firstChange.trans secondChange).reading τ)
        ((firstChange.trans secondChange).outcome a)| ≤
      firstChange.error + secondChange.error :=
  (firstChange.trans secondChange).controlled τ a

end PhysicsModel.QuantumClockError
