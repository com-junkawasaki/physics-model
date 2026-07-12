import PhysicsModel.CurvatureError
import Mathlib.Tactic.Linarith

/-! # Error propagation through curvature contractions to Einstein's tensor -/

namespace PhysicsModel.EinsteinError

open scoped BigOperators
open PhysicsModel.Geometry4
open PhysicsModel.ConnectionError

/-- Contracting four Riemann components multiplies the component error by four. -/
theorem ricci_component_error (fine coarse : RiemannTensor) (εCurvature : ℝ)
    (controlled : ∀ ρ σ μ ν,
      |fine ρ σ μ ν - coarse ρ σ μ ν| ≤ εCurvature)
    (σ ν : Index) :
    |ricci fine σ ν - ricci coarse σ ν| ≤ 4 * εCurvature := by
  unfold ricci
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ ρ, (fine ρ σ ρ ν - coarse ρ σ ρ ν)| ≤ ∑ _ρ : Index, εCurvature :=
      le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun ρ _ => controlled ρ σ ρ ν)
    _ = 4 * εCurvature := by simp

/-- Sixteen inverse-metric/Ricci products control scalar-curvature refinement error. -/
theorem scalarCurvature_error
    (fineInverse coarseInverse : Metric) (fineCurvature coarseCurvature : RiemannTensor)
    (εInverse εCurvature inverseBound coarseRicciBound : ℝ)
    (hεInverse : 0 ≤ εInverse) (hInverseBound : 0 ≤ inverseBound)
    (inverseError : ∀ μ ν, |fineInverse μ ν - coarseInverse μ ν| ≤ εInverse)
    (curvatureError : ∀ ρ σ μ ν,
      |fineCurvature ρ σ μ ν - coarseCurvature ρ σ μ ν| ≤ εCurvature)
    (fineInverseBound : ∀ μ ν, |fineInverse μ ν| ≤ inverseBound)
    (ricciBound : ∀ μ ν, |ricci coarseCurvature μ ν| ≤ coarseRicciBound) :
    |scalarCurvature fineInverse (ricci fineCurvature) -
      scalarCurvature coarseInverse (ricci coarseCurvature)| ≤
        16 * (εInverse * coarseRicciBound + inverseBound * (4 * εCurvature)) := by
  let E := εInverse * coarseRicciBound + inverseBound * (4 * εCurvature)
  have hterm : ∀ μ ν,
      |fineInverse μ ν * ricci fineCurvature μ ν -
        coarseInverse μ ν * ricci coarseCurvature μ ν| ≤ E := by
    intro μ ν
    exact abs_mul_sub_mul_le _ _ _ _ _ _ _ _ (inverseError μ ν)
      (ricci_component_error fineCurvature coarseCurvature εCurvature curvatureError μ ν)
      (fineInverseBound μ ν) (ricciBound μ ν) hεInverse hInverseBound
  unfold scalarCurvature
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    |∑ μ, ∑ ν, (fineInverse μ ν * ricci fineCurvature μ ν -
        coarseInverse μ ν * ricci coarseCurvature μ ν)| ≤
        ∑ _μ : Index, ∑ _ν : Index, E := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      apply Finset.sum_le_sum
      intro μ _
      exact le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun ν _ => hterm μ ν)
    _ = 16 * (εInverse * coarseRicciBound + inverseBound * (4 * εCurvature)) := by
      simp [E]
      ring

/-- Stability of `Gμν = Rμν - ½ R gμν` under simultaneous refinement. -/
theorem einsteinTensor_component_error
    (fineMetric coarseMetric fineInverse coarseInverse : Metric)
    (fineCurvature coarseCurvature : RiemannTensor)
    (εMetric εCurvature εScalar scalarBound coarseMetricBound : ℝ)
    (hεScalar : 0 ≤ εScalar) (hScalarBound : 0 ≤ scalarBound)
    (metricError : ∀ μ ν, |fineMetric μ ν - coarseMetric μ ν| ≤ εMetric)
    (curvatureError : ∀ ρ σ μ ν,
      |fineCurvature ρ σ μ ν - coarseCurvature ρ σ μ ν| ≤ εCurvature)
    (scalarError :
      |scalarCurvature fineInverse (ricci fineCurvature) -
        scalarCurvature coarseInverse (ricci coarseCurvature)| ≤ εScalar)
    (fineScalarBound : |scalarCurvature fineInverse (ricci fineCurvature)| ≤ scalarBound)
    (metricBound : ∀ μ ν, |coarseMetric μ ν| ≤ coarseMetricBound)
    (μ ν : Index) :
    |einsteinTensor fineMetric fineInverse fineCurvature μ ν -
      einsteinTensor coarseMetric coarseInverse coarseCurvature μ ν| ≤
        4 * εCurvature +
          (1 / 2 : ℝ) * (εScalar * coarseMetricBound + scalarBound * εMetric) := by
  have hRicci := ricci_component_error fineCurvature coarseCurvature εCurvature
    curvatureError μ ν
  have hProduct := abs_mul_sub_mul_le
    (scalarCurvature fineInverse (ricci fineCurvature)) (fineMetric μ ν)
    (scalarCurvature coarseInverse (ricci coarseCurvature)) (coarseMetric μ ν)
    εScalar εMetric scalarBound coarseMetricBound scalarError (metricError μ ν)
    fineScalarBound (metricBound μ ν) hεScalar hScalarBound
  unfold einsteinTensor
  have heq :
      (ricci fineCurvature μ ν - (1 / 2 : ℝ) *
          scalarCurvature fineInverse (ricci fineCurvature) * fineMetric μ ν) -
        (ricci coarseCurvature μ ν - (1 / 2 : ℝ) *
          scalarCurvature coarseInverse (ricci coarseCurvature) * coarseMetric μ ν) =
      (ricci fineCurvature μ ν - ricci coarseCurvature μ ν) -
        (1 / 2 : ℝ) *
          (scalarCurvature fineInverse (ricci fineCurvature) * fineMetric μ ν -
            scalarCurvature coarseInverse (ricci coarseCurvature) * coarseMetric μ ν) := by ring
  rw [heq]
  calc
    |(ricci fineCurvature μ ν - ricci coarseCurvature μ ν) -
        (1 / 2 : ℝ) *
          (scalarCurvature fineInverse (ricci fineCurvature) * fineMetric μ ν -
            scalarCurvature coarseInverse (ricci coarseCurvature) * coarseMetric μ ν)| ≤
      |ricci fineCurvature μ ν - ricci coarseCurvature μ ν| +
        |(1 / 2 : ℝ) *
          (scalarCurvature fineInverse (ricci fineCurvature) * fineMetric μ ν -
            scalarCurvature coarseInverse (ricci coarseCurvature) * coarseMetric μ ν)| := abs_sub _ _
    _ ≤ 4 * εCurvature +
        (1 / 2 : ℝ) * (εScalar * coarseMetricBound + scalarBound * εMetric) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact add_le_add hRicci (mul_le_mul_of_nonneg_left hProduct (by norm_num))

/-- One component of `G + Λg - κT`, the effective Einstein equation residual. -/
noncomputable def fieldResidual (metric inverseMetric : Metric) (curvature : RiemannTensor)
    (stressEnergy : Metric) (cosmologicalConstant coupling : ℝ) : Metric :=
  fun μ ν => einsteinTensor metric inverseMetric curvature μ ν +
    cosmologicalConstant * metric μ ν - coupling * stressEnergy μ ν

/-- Geometric, metric, and matter refinement errors control the full field residual. -/
theorem fieldResidual_component_error
    (fineMetric coarseMetric fineInverse coarseInverse : Metric)
    (fineCurvature coarseCurvature : RiemannTensor)
    (fineStress coarseStress : Metric) (cosmologicalConstant coupling : ℝ)
    (εEinstein εMetric εStress : ℝ)
    (einsteinError : ∀ μ ν,
      |einsteinTensor fineMetric fineInverse fineCurvature μ ν -
        einsteinTensor coarseMetric coarseInverse coarseCurvature μ ν| ≤ εEinstein)
    (metricError : ∀ μ ν, |fineMetric μ ν - coarseMetric μ ν| ≤ εMetric)
    (stressError : ∀ μ ν, |fineStress μ ν - coarseStress μ ν| ≤ εStress)
    (μ ν : Index) :
    |fieldResidual fineMetric fineInverse fineCurvature fineStress cosmologicalConstant coupling μ ν -
      fieldResidual coarseMetric coarseInverse coarseCurvature coarseStress cosmologicalConstant coupling μ ν| ≤
        εEinstein + |cosmologicalConstant| * εMetric + |coupling| * εStress := by
  have hG := einsteinError μ ν
  have hg := metricError μ ν
  have hT := stressError μ ν
  unfold fieldResidual
  have heq :
      (einsteinTensor fineMetric fineInverse fineCurvature μ ν +
          cosmologicalConstant * fineMetric μ ν - coupling * fineStress μ ν) -
        (einsteinTensor coarseMetric coarseInverse coarseCurvature μ ν +
          cosmologicalConstant * coarseMetric μ ν - coupling * coarseStress μ ν) =
      (einsteinTensor fineMetric fineInverse fineCurvature μ ν -
          einsteinTensor coarseMetric coarseInverse coarseCurvature μ ν) +
        cosmologicalConstant * (fineMetric μ ν - coarseMetric μ ν) -
        coupling * (fineStress μ ν - coarseStress μ ν) := by ring
  rw [heq]
  calc
    |(einsteinTensor fineMetric fineInverse fineCurvature μ ν -
          einsteinTensor coarseMetric coarseInverse coarseCurvature μ ν) +
        cosmologicalConstant * (fineMetric μ ν - coarseMetric μ ν) -
        coupling * (fineStress μ ν - coarseStress μ ν)| ≤
      |einsteinTensor fineMetric fineInverse fineCurvature μ ν -
          einsteinTensor coarseMetric coarseInverse coarseCurvature μ ν| +
        |cosmologicalConstant * (fineMetric μ ν - coarseMetric μ ν)| +
        |coupling * (fineStress μ ν - coarseStress μ ν)| := by
          exact le_trans (abs_sub _ _) (add_le_add_right (abs_add _ _) _)
    _ ≤ εEinstein + |cosmologicalConstant| * εMetric + |coupling| * εStress := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add hG (mul_le_mul_of_nonneg_left hg (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hT (abs_nonneg _))

end PhysicsModel.EinsteinError
