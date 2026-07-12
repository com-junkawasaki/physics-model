import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Schwarzschild black-hole thermodynamics and evaporation

We use natural units `c = ħ = k_B = 1`, retaining Newton's constant `G`.
The module checks the exact algebra connecting horizon geometry, entropy,
temperature, the first law, and the semiclassical `M³` evaporation timescale.
-/

namespace PhysicsModel.BlackHole

/-- Schwarzschild radius `r_s = 2GM`. -/
noncomputable def radius (G mass : ℝ) : ℝ := 2 * G * mass

/-- Horizon area `A = 4πr_s²`. -/
noncomputable def area (G mass : ℝ) : ℝ := 4 * Real.pi * radius G mass ^ 2

/-- Bekenstein--Hawking entropy `S = A/(4G)`. -/
noncomputable def entropy (G mass : ℝ) : ℝ := area G mass / (4 * G)

theorem area_eq (G mass : ℝ) :
    area G mass = 16 * Real.pi * G ^ 2 * mass ^ 2 := by
  unfold area radius
  ring

theorem entropy_eq {G : ℝ} (mass : ℝ) (G_nonzero : G ≠ 0) :
    entropy G mass = 4 * Real.pi * G * mass ^ 2 := by
  rw [entropy, area_eq]
  field_simp
  ring

/-- Hawking temperature `T_H = 1/(8πGM)`. -/
noncomputable def temperature (G mass : ℝ) : ℝ :=
  1 / (8 * Real.pi * G * mass)

theorem radius_positive {G mass : ℝ} (G_positive : 0 < G)
    (mass_positive : 0 < mass) : 0 < radius G mass := by
  unfold radius
  positivity

theorem area_positive {G mass : ℝ} (G_positive : 0 < G)
    (mass_positive : 0 < mass) : 0 < area G mass := by
  rw [area_eq]
  positivity

theorem entropy_positive {G mass : ℝ} (G_positive : 0 < G)
    (mass_positive : 0 < mass) : 0 < entropy G mass := by
  rw [entropy_eq mass (ne_of_gt G_positive)]
  positivity

theorem temperature_positive {G mass : ℝ} (G_positive : 0 < G)
    (mass_positive : 0 < mass) : 0 < temperature G mass := by
  unfold temperature
  positivity

/-- Exact slope `dS/dM` of the quadratic entropy formula. -/
noncomputable def entropySlope (G mass : ℝ) : ℝ :=
  8 * Real.pi * G * mass

/-- Black-hole first law `T_H (dS/dM) = 1`. -/
theorem first_law {G mass : ℝ} (G_nonzero : G ≠ 0) (mass_nonzero : mass ≠ 0) :
    temperature G mass * entropySlope G mass = 1 := by
  unfold temperature entropySlope
  field_simp [Real.pi_ne_zero, G_nonzero, mass_nonzero]

/-- Schwarzschild heat capacity `C = dM/dT = -8πGM²`. -/
noncomputable def heatCapacity (G mass : ℝ) : ℝ :=
  -8 * Real.pi * G * mass ^ 2

theorem heatCapacity_negative {G mass : ℝ} (G_positive : 0 < G)
    (mass_nonzero : mass ≠ 0) : heatCapacity G mass < 0 := by
  unfold heatCapacity
  have hm : 0 < mass ^ 2 := sq_pos_of_ne_zero mass_nonzero
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num : (-8 : ℝ) < 0) Real.pi_pos)
      G_positive)
    hm

/-- Temperature slope `dT/dM`, inverse to the heat capacity. -/
noncomputable def temperatureSlope (G mass : ℝ) : ℝ :=
  -1 / (8 * Real.pi * G * mass ^ 2)

theorem heatCapacity_temperatureSlope {G mass : ℝ}
    (G_nonzero : G ≠ 0) (mass_nonzero : mass ≠ 0) :
    heatCapacity G mass * temperatureSlope G mass = 1 := by
  unfold heatCapacity temperatureSlope
  field_simp [Real.pi_ne_zero, G_nonzero, mass_nonzero]

/-- Semiclassical mass-loss rate `dM/dt = -α/M²`. -/
noncomputable def evaporationRate (alpha mass : ℝ) : ℝ :=
  -alpha / mass ^ 2

theorem evaporationRate_negative {alpha mass : ℝ} (alpha_positive : 0 < alpha)
    (mass_nonzero : mass ≠ 0) : evaporationRate alpha mass < 0 := by
  unfold evaporationRate
  exact div_neg_of_neg_of_pos (neg_neg_of_pos alpha_positive) (sq_pos_of_ne_zero mass_nonzero)

/-- Along evaporation, entropy decreases locally. -/
theorem entropy_rate_negative {G alpha mass : ℝ}
    (G_positive : 0 < G) (alpha_positive : 0 < alpha) (mass_positive : 0 < mass) :
    entropySlope G mass * evaporationRate alpha mass < 0 :=
  mul_neg_of_pos_of_neg (by unfold entropySlope; positivity)
    (evaporationRate_negative alpha_positive (ne_of_gt mass_positive))

/-- Chain-rule rate for `M³`: `d(M³)/dt = 3M² dM/dt`. -/
noncomputable def massCubedRate (alpha mass : ℝ) : ℝ :=
  3 * mass ^ 2 * evaporationRate alpha mass

theorem massCubedRate_eq {alpha mass : ℝ} (mass_nonzero : mass ≠ 0) :
    massCubedRate alpha mass = -3 * alpha := by
  unfold massCubedRate evaporationRate
  field_simp

/-- Integrated evaporation timescale `τ = M₀³/(3α)`. -/
noncomputable def evaporationLifetime (alpha initialMass : ℝ) : ℝ :=
  initialMass ^ 3 / (3 * alpha)

theorem evaporationLifetime_positive {alpha initialMass : ℝ}
    (alpha_positive : 0 < alpha) (mass_positive : 0 < initialMass) :
    0 < evaporationLifetime alpha initialMass := by
  unfold evaporationLifetime
  positivity

/-- The lifetime exactly cancels the constant cubic-mass loss. -/
theorem lifetime_balance {alpha initialMass : ℝ} (alpha_nonzero : alpha ≠ 0) :
    3 * alpha * evaporationLifetime alpha initialMass = initialMass ^ 3 := by
  unfold evaporationLifetime
  field_simp

end PhysicsModel.BlackHole
