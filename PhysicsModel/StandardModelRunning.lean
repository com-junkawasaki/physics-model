import PhysicsModel.ElectroweakCharges
import PhysicsModel.RunningCoupling
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-! # Standard Model one-loop running-coupling coefficients

The one-loop coefficients are written as explicit weighted sums over the
Standard Model matter content.  This module checks the exact rational numerators
for the `SU(3)`, `SU(2)`, and `U(1)` beta functions in the convention used by
`PhysicsModel.RunningCoupling`.
-/

namespace PhysicsModel.StandardModelRunning

open PhysicsModel.Electroweak

private def su3FundamentalIndex : ℚ := 1 / 2
private def su2FundamentalIndex : ℚ := 1 / 2

private def su3FermionIndexPerGeneration : ℚ :=
  2 * su3FundamentalIndex + su3FundamentalIndex + su3FundamentalIndex

private def su3FermionIndexAll : ℚ :=
  3 * su3FermionIndexPerGeneration

private def su2FermionIndexPerGeneration : ℚ :=
  3 * su2FundamentalIndex + su2FundamentalIndex

private def su2FermionIndexAll : ℚ :=
  3 * su2FermionIndexPerGeneration

private def higgsDoubletIndex : ℚ := 1 / 2

private def u1FermionHyperchargeSqPerGeneration : ℚ :=
  6 * leftQuark.hypercharge ^ 2 +
    3 * rightUp.hypercharge ^ 2 +
    3 * rightDown.hypercharge ^ 2 +
    2 * leftLepton.hypercharge ^ 2 +
    rightElectron.hypercharge ^ 2

private def u1FermionHyperchargeSqAll : ℚ :=
  3 * u1FermionHyperchargeSqPerGeneration

private def u1ScalarHyperchargeSq : ℚ :=
  2 * higgs.hypercharge ^ 2

/-- The `SU(3)` fermion index is `2` per generation and `6` over three generations. -/
theorem su3_fermion_index_per_generation : su3FermionIndexPerGeneration = 2 := by
  norm_num [su3FermionIndexPerGeneration, su3FundamentalIndex]

theorem su3_fermion_index_all : su3FermionIndexAll = 6 := by
  norm_num [su3FermionIndexAll, su3FermionIndexPerGeneration, su3FundamentalIndex]

/-- The `SU(2)` fermion index is `2` per generation and `6` over three generations. -/
theorem su2_fermion_index_per_generation : su2FermionIndexPerGeneration = 2 := by
  norm_num [su2FermionIndexPerGeneration, su2FundamentalIndex]

theorem su2_fermion_index_all : su2FermionIndexAll = 6 := by
  norm_num [su2FermionIndexAll, su2FermionIndexPerGeneration, su2FundamentalIndex]

/-- The Higgs doublet contributes one half to the `SU(2)` scalar index. -/
theorem higgs_doublet_index : higgsDoubletIndex = 1 / 2 := by
  rfl

/-- The total `U(1)` hypercharge-squared sum over fermions is `10` over three generations. -/
theorem u1_fermion_hypercharge_sq_all : u1FermionHyperchargeSqAll = 10 := by
  norm_num [u1FermionHyperchargeSqAll, u1FermionHyperchargeSqPerGeneration,
    leftQuark, rightUp, rightDown, leftLepton, rightElectron]

/-- The Higgs scalar contributes `1/2` to the `U(1)` hypercharge-squared sum. -/
theorem u1_scalar_hypercharge_sq : u1ScalarHyperchargeSq = 1 / 2 := by
  norm_num [u1ScalarHyperchargeSq, higgs]

/-- The `SU(3)` one-loop beta numerator in this convention is `7`. -/
def su3BetaNumerator : ℚ :=
  11 / 3 * 3 - 2 / 3 * su3FermionIndexAll

/-- The `SU(2)` one-loop beta numerator in this convention is `19/6`. -/
def su2BetaNumerator : ℚ :=
  22 / 3 - 2 / 3 * su2FermionIndexAll - 1 / 3 * higgsDoubletIndex

/-- The `U(1)` one-loop beta numerator in this convention is `-41/6`. -/
def u1BetaNumerator : ℚ :=
  - (2 / 3 * u1FermionHyperchargeSqAll + 1 / 3 * u1ScalarHyperchargeSq)

theorem su3_beta_numerator : su3BetaNumerator = 7 := by
  norm_num [su3BetaNumerator, su3_fermion_index_all]

theorem su2_beta_numerator : su2BetaNumerator = 19 / 6 := by
  norm_num [su2BetaNumerator, su2_fermion_index_all, higgs_doublet_index]

theorem u1_beta_numerator : u1BetaNumerator = -41 / 6 := by
  norm_num [u1BetaNumerator, u1_fermion_hypercharge_sq_all, u1_scalar_hypercharge_sq]

/-- Normalize a rational one-loop numerator to the `RunningCoupling` coefficient convention. -/
noncomputable def betaCoefficient (numerator : ℚ) : ℝ :=
  (numerator : ℝ) / (8 * Real.pi ^ 2)

theorem betaCoefficient_pos {numerator : ℚ}
    (hn : 0 < numerator) : 0 < betaCoefficient numerator := by
  unfold betaCoefficient
  have hpi : 0 < (8 * Real.pi ^ 2 : ℝ) := by
    positivity
  exact div_pos (by exact_mod_cast hn) hpi

theorem betaCoefficient_neg {numerator : ℚ}
    (hn : numerator < 0) : betaCoefficient numerator < 0 := by
  unfold betaCoefficient
  have hpi : 0 < (8 * Real.pi ^ 2 : ℝ) := by
    positivity
  exact div_neg_of_neg_of_pos (by exact_mod_cast hn) hpi

/-- The `SU(3)` coefficient is positive, so the coupling is asymptotically free. -/
theorem su3_betaCoefficient_positive : 0 < betaCoefficient su3BetaNumerator := by
  rw [su3_beta_numerator]
  apply betaCoefficient_pos
  norm_num

/-- The `SU(2)` coefficient is positive, so the coupling is asymptotically free. -/
theorem su2_betaCoefficient_positive : 0 < betaCoefficient su2BetaNumerator := by
  rw [su2_beta_numerator]
  apply betaCoefficient_pos
  norm_num

/-- The hypercharge coefficient is negative, so it has a Landau-pole branch. -/
theorem u1_betaCoefficient_negative : betaCoefficient u1BetaNumerator < 0 := by
  rw [u1_beta_numerator]
  apply betaCoefficient_neg
  norm_num

/-- The `SU(3)` coefficient in `RunningCoupling` form is `7 / (8 π^2)`. -/
theorem su3_betaCoefficient_value :
    betaCoefficient su3BetaNumerator = 7 / (8 * Real.pi ^ 2) := by
  rw [su3_beta_numerator, betaCoefficient]
  norm_num

/-- The `SU(2)` coefficient in `RunningCoupling` form is `(19/6) / (8 π^2)`. -/
theorem su2_betaCoefficient_value :
    betaCoefficient su2BetaNumerator = (19 / 6) / (8 * Real.pi ^ 2) := by
  rw [su2_beta_numerator, betaCoefficient]
  norm_num

/-- The `U(1)` coefficient in `RunningCoupling` form is `(-41/6) / (8 π^2)`. -/
theorem u1_betaCoefficient_value :
    betaCoefficient u1BetaNumerator = (-41 / 6) / (8 * Real.pi ^ 2) := by
  rw [u1_beta_numerator, betaCoefficient]
  norm_num

/-- The `SU(3)` running coupling decreases with scale whenever the denominator stays positive. -/
theorem su3_asymptotic_freedom
    {initialInverse t₁ t₂ : ℝ}
    (timeOrder : t₁ ≤ t₂)
    (denominatorPositive : 0 < RunningCoupling.inverseCouplingSq
      initialInverse (betaCoefficient su3BetaNumerator) t₁) :
    RunningCoupling.couplingSq initialInverse (betaCoefficient su3BetaNumerator) t₂ ≤
      RunningCoupling.couplingSq initialInverse (betaCoefficient su3BetaNumerator) t₁ :=
  RunningCoupling.asymptotic_freedom_monotone
    (betaPositive := by simpa using su3_betaCoefficient_positive)
    timeOrder denominatorPositive

/-- The `SU(2)` running coupling decreases with scale whenever the denominator stays positive. -/
theorem su2_asymptotic_freedom
    {initialInverse t₁ t₂ : ℝ}
    (timeOrder : t₁ ≤ t₂)
    (denominatorPositive : 0 < RunningCoupling.inverseCouplingSq
      initialInverse (betaCoefficient su2BetaNumerator) t₁) :
    RunningCoupling.couplingSq initialInverse (betaCoefficient su2BetaNumerator) t₂ ≤
      RunningCoupling.couplingSq initialInverse (betaCoefficient su2BetaNumerator) t₁ :=
  RunningCoupling.asymptotic_freedom_monotone
    (betaPositive := by simpa using su2_betaCoefficient_positive)
    timeOrder denominatorPositive

/-- The `U(1)` running coupling reaches a pole at finite positive RG time. -/
theorem u1_landau_pole_time_positive {initialInverse : ℝ}
    (initialPositive : 0 < initialInverse) :
    0 < RunningCoupling.landauPoleTime initialInverse (betaCoefficient u1BetaNumerator) := by
  exact RunningCoupling.landauPoleTime_positive initialPositive u1_betaCoefficient_negative

theorem u1_landau_pole_denominator_zero {initialInverse : ℝ} :
    RunningCoupling.inverseCouplingSq initialInverse (betaCoefficient u1BetaNumerator)
      (RunningCoupling.landauPoleTime initialInverse (betaCoefficient u1BetaNumerator)) = 0 := by
  exact RunningCoupling.landauPole_denominator_zero u1_betaCoefficient_negative

/-- The Standard Model one-loop RG pattern: two asymptotically free couplings and one Landau-pole branch. -/
theorem standardModel_one_loop_rg_pattern :
    (0 < betaCoefficient su3BetaNumerator) ∧
    (0 < betaCoefficient su2BetaNumerator) ∧
    (betaCoefficient u1BetaNumerator < 0) := by
  exact ⟨su3_betaCoefficient_positive, su2_betaCoefficient_positive,
    u1_betaCoefficient_negative⟩

/-- The exact one-loop coefficient values are fixed by the checked particle content. -/
theorem standardModel_one_loop_coefficients :
    betaCoefficient su3BetaNumerator = 7 / (8 * Real.pi ^ 2) ∧
    betaCoefficient su2BetaNumerator = (19 / 6) / (8 * Real.pi ^ 2) ∧
    betaCoefficient u1BetaNumerator = (-41 / 6) / (8 * Real.pi ^ 2) := by
  exact ⟨su3_betaCoefficient_value, su2_betaCoefficient_value, u1_betaCoefficient_value⟩

end PhysicsModel.StandardModelRunning
