import PhysicsModel.ApproximateRefinement
import Mathlib.Tactic.Linarith

/-! # Error propagation from coarse metrics to Levi--Civita connections

The Christoffel kernel is bilinear in the inverse metric and the first metric
derivatives.  The estimates below make the resulting finite-dimensional error
propagation explicit, without hiding a continuity assumption.
-/

namespace PhysicsModel.ConnectionError

open scoped BigOperators
open PhysicsModel.Geometry4
open PhysicsModel.CoarseGeometry4

/-- The derivative combination occurring in the Levi--Civita formula. -/
def derivativeBracket (derivative : MetricDerivative) (μ ν σ : Index) : ℝ :=
  derivative μ σ ν + derivative ν σ μ - derivative σ μ ν

/-- The elementary product perturbation estimate used by the Christoffel sum. -/
theorem abs_mul_sub_mul_le (a b c d εa εb A B : ℝ)
    (ha : |a - c| ≤ εa) (hb : |b - d| ≤ εb)
    (hA : |a| ≤ A) (hB : |d| ≤ B)
    (hεa : 0 ≤ εa) (hA0 : 0 ≤ A) :
    |a * b - c * d| ≤ εa * B + A * εb := by
  have hid : a * b - c * d = (a - c) * d + a * (b - d) := by ring
  rw [hid]
  calc
    |(a - c) * d + a * (b - d)| ≤ |(a - c) * d| + |a * (b - d)| := abs_add _ _
    _ = |a - c| * |d| + |a| * |b - d| := by rw [abs_mul, abs_mul]
    _ ≤ εa * B + A * εb := by
      exact add_le_add (mul_le_mul ha hB (abs_nonneg _) hεa)
        (mul_le_mul hA hb (abs_nonneg _) hA0)

/-- Componentwise first-derivative error controls the three-term Christoffel bracket. -/
theorem derivativeBracket_error (fine coarse : MetricDerivative) (ε : ℝ)
    (controlled : ∀ direction μ ν,
      |fine direction μ ν - coarse direction μ ν| ≤ ε)
    (μ ν σ : Index) :
    |derivativeBracket fine μ ν σ - derivativeBracket coarse μ ν σ| ≤ 3 * ε := by
  have h1 := controlled μ σ ν
  have h2 := controlled ν σ μ
  have h3 := controlled σ μ ν
  have hadd := abs_add (fine μ σ ν - coarse μ σ ν)
    (fine ν σ μ - coarse ν σ μ)
  have hsub := abs_sub
    ((fine μ σ ν - coarse μ σ ν) +
      (fine ν σ μ - coarse ν σ μ))
    (fine σ μ ν - coarse σ μ ν)
  unfold derivativeBracket
  have heq :
      fine μ σ ν + fine ν σ μ - fine σ μ ν -
          (coarse μ σ ν + coarse ν σ μ - coarse σ μ ν) =
        (fine μ σ ν - coarse μ σ ν) +
          (fine ν σ μ - coarse ν σ μ) -
          (fine σ μ ν - coarse σ μ ν) := by ring
  rw [heq]
  linarith

/-- Explicit stability bound for every Levi--Civita connection coefficient. -/
theorem leviCivita_component_error
    (fineInverse coarseInverse : Metric) (fineDerivative coarseDerivative : MetricDerivative)
    (εInverse εBracket inverseBound bracketBound : ℝ)
    (hεInverse : 0 ≤ εInverse) (hεBracket : 0 ≤ εBracket)
    (hInverseBound : 0 ≤ inverseBound) (hBracketBound : 0 ≤ bracketBound)
    (inverseError : ∀ ρ σ, |fineInverse ρ σ - coarseInverse ρ σ| ≤ εInverse)
    (bracketError : ∀ μ ν σ,
      |derivativeBracket fineDerivative μ ν σ -
        derivativeBracket coarseDerivative μ ν σ| ≤ εBracket)
    (fineInverseBound : ∀ ρ σ, |fineInverse ρ σ| ≤ inverseBound)
    (coarseBracketBound : ∀ μ ν σ,
      |derivativeBracket coarseDerivative μ ν σ| ≤ bracketBound)
    (ρ μ ν : Index) :
    |leviCivita fineInverse fineDerivative ρ μ ν -
      leviCivita coarseInverse coarseDerivative ρ μ ν| ≤
        2 * (εInverse * bracketBound + inverseBound * εBracket) := by
  let E := εInverse * bracketBound + inverseBound * εBracket
  have hE : 0 ≤ E := add_nonneg (mul_nonneg hεInverse hBracketBound)
    (mul_nonneg hInverseBound hεBracket)
  have hterm : ∀ σ,
      |fineInverse ρ σ * derivativeBracket fineDerivative μ ν σ -
        coarseInverse ρ σ * derivativeBracket coarseDerivative μ ν σ| ≤ E := by
    intro σ
    exact abs_mul_sub_mul_le _ _ _ _ _ _ _ _ (inverseError ρ σ)
      (bracketError μ ν σ) (fineInverseBound ρ σ)
      (coarseBracketBound μ ν σ) hεInverse hInverseBound
  unfold leviCivita
  change |(1 / 2 : ℝ) * ∑ σ, fineInverse ρ σ * derivativeBracket fineDerivative μ ν σ -
      (1 / 2 : ℝ) * ∑ σ, coarseInverse ρ σ * derivativeBracket coarseDerivative μ ν σ| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [← Finset.sum_sub_distrib]
  calc
    (1 / 2 : ℝ) * |∑ σ, (fineInverse ρ σ * derivativeBracket fineDerivative μ ν σ -
        coarseInverse ρ σ * derivativeBracket coarseDerivative μ ν σ)| ≤
        (1 / 2 : ℝ) * ∑ _σ : Index, E := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun σ _ => hterm σ)
    _ = 2 * (εInverse * bracketBound + inverseBound * εBracket) := by
      simp [E]
      ring

end PhysicsModel.ConnectionError
