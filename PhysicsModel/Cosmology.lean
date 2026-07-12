import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Slow-roll cosmological observables

This module records the leading-order single-field inflationary predictions in
natural units.  It checks positivity, power-law scaling, the scalar/tensor
amplitude ratio, and the observable consistency relation `r = -8 n_t`.
-/

namespace PhysicsModel.Cosmology

/-- Leading scalar curvature-perturbation amplitude at horizon exit. -/
noncomputable def scalarAmplitude (hubble epsilon planckMass : ℝ) : ℝ :=
  hubble ^ 2 / (8 * Real.pi ^ 2 * epsilon * planckMass ^ 2)

/-- Leading primordial tensor amplitude. -/
noncomputable def tensorAmplitude (hubble planckMass : ℝ) : ℝ :=
  2 * hubble ^ 2 / (Real.pi ^ 2 * planckMass ^ 2)

/-- Scalar spectral index `n_s = 1 - 6ε + 2η`. -/
noncomputable def scalarSpectralIndex (epsilon eta : ℝ) : ℝ :=
  1 - 6 * epsilon + 2 * eta

/-- Tensor spectral tilt `n_t = -2ε`. -/
noncomputable def tensorTilt (epsilon : ℝ) : ℝ := -2 * epsilon

/-- Predicted tensor-to-scalar ratio `r = 16ε`. -/
noncomputable def tensorToScalarRatio (epsilon : ℝ) : ℝ := 16 * epsilon

theorem scalarAmplitude_positive {hubble epsilon planckMass : ℝ}
    (hubble_nonzero : hubble ≠ 0) (epsilon_positive : 0 < epsilon)
    (planck_nonzero : planckMass ≠ 0) :
    0 < scalarAmplitude hubble epsilon planckMass := by
  unfold scalarAmplitude
  positivity

theorem tensorAmplitude_positive {hubble planckMass : ℝ}
    (hubble_nonzero : hubble ≠ 0) (planck_nonzero : planckMass ≠ 0) :
    0 < tensorAmplitude hubble planckMass := by
  unfold tensorAmplitude
  positivity

/-- Direct ratio of tensor and scalar amplitudes gives `16ε`. -/
theorem amplitude_ratio {hubble epsilon planckMass : ℝ}
    (hubble_nonzero : hubble ≠ 0) (epsilon_nonzero : epsilon ≠ 0)
    (planck_nonzero : planckMass ≠ 0) :
    tensorAmplitude hubble planckMass /
        scalarAmplitude hubble epsilon planckMass =
      tensorToScalarRatio epsilon := by
  unfold tensorAmplitude scalarAmplitude tensorToScalarRatio
  field_simp [Real.pi_ne_zero, hubble_nonzero, epsilon_nonzero, planck_nonzero]
  ring

/-- Single-field slow-roll consistency relation. -/
theorem single_field_consistency (epsilon : ℝ) :
    tensorToScalarRatio epsilon = -8 * tensorTilt epsilon := by
  unfold tensorToScalarRatio tensorTilt
  ring

theorem ratio_nonnegative {epsilon : ℝ} (epsilon_nonnegative : 0 ≤ epsilon) :
    0 ≤ tensorToScalarRatio epsilon := by
  unfold tensorToScalarRatio
  positivity

theorem red_tensor_tilt {epsilon : ℝ} (epsilon_positive : 0 < epsilon) :
    tensorTilt epsilon < 0 := by
  unfold tensorTilt
  exact mul_neg_of_neg_of_pos (by norm_num) epsilon_positive

/-- Power-law scalar spectrum around pivot scale `k_*`. -/
noncomputable def powerSpectrum
    (amplitude spectralIndex pivotScale waveNumber : ℝ) : ℝ :=
  amplitude * (waveNumber / pivotScale) ^ (spectralIndex - 1)

theorem powerSpectrum_at_pivot (amplitude spectralIndex : ℝ)
    {pivotScale : ℝ} (pivot_positive : 0 < pivotScale) :
    powerSpectrum amplitude spectralIndex pivotScale pivotScale = amplitude := by
  unfold powerSpectrum
  rw [div_self (ne_of_gt pivot_positive)]
  simp

/-- Exact scale invariance (`n_s=1`) makes the spectrum independent of `k`. -/
theorem scale_invariant_spectrum (amplitude pivotScale waveNumber : ℝ) :
    powerSpectrum amplitude 1 pivotScale waveNumber = amplitude := by
  simp [powerSpectrum]

theorem powerSpectrum_positive {amplitude spectralIndex pivotScale waveNumber : ℝ}
    (amplitude_positive : 0 < amplitude) (pivot_positive : 0 < pivotScale)
    (waveNumber_positive : 0 < waveNumber) :
    0 < powerSpectrum amplitude spectralIndex pivotScale waveNumber := by
  unfold powerSpectrum
  apply mul_pos amplitude_positive
  exact Real.rpow_pos_of_pos (div_pos waveNumber_positive pivot_positive) _

/-- A measured `(r,n_t)` pair falsifies leading single-field slow roll if this residual is nonzero. -/
noncomputable def consistencyResidual (r tensorSpectralTilt : ℝ) : ℝ :=
  r + 8 * tensorSpectralTilt

theorem predicted_consistencyResidual_zero (epsilon : ℝ) :
    consistencyResidual (tensorToScalarRatio epsilon) (tensorTilt epsilon) = 0 := by
  unfold consistencyResidual tensorToScalarRatio tensorTilt
  ring

end PhysicsModel.Cosmology
