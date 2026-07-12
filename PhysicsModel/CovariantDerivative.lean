import PhysicsModel.Conservation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! # Component covariant derivative and contracted divergence

This module replaces the abstract divergence certificate by its finite
four-dimensional component formula.  A linear partial-derivative operator and
connection coefficients determine `∇_λ T_{μν}`; contraction with the inverse
metric determines `∇^μ T_{μν}`.
-/

namespace PhysicsModel.CovariantDerivative

open scoped BigOperators
open PhysicsModel.Geometry4

/-- Linear local partial derivative of a rank-two tensor. -/
abbrev PartialOperator := Metric →ₗ[ℝ] (Index → Metric)

/-- Covariant derivative of a covariant rank-two tensor. -/
def covariantDerivative (connection : Connection) (partialOp : PartialOperator)
    (tensor : Metric) (direction μ ν : Index) : ℝ :=
  partialOp tensor direction μ ν -
    (∑ ρ, connection ρ direction μ * tensor ρ ν) -
    ∑ ρ, connection ρ direction ν * tensor μ ρ

theorem covariantDerivative_add (connection : Connection) (partialOp : PartialOperator)
    (first second : Metric) :
    covariantDerivative connection partialOp (first + second) =
      covariantDerivative connection partialOp first +
        covariantDerivative connection partialOp second := by
  funext direction μ ν
  have hμ :
      (∑ ρ, connection ρ direction μ * (first + second) ρ ν) =
        (∑ ρ, connection ρ direction μ * first ρ ν) +
          ∑ ρ, connection ρ direction μ * second ρ ν := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    simp [mul_add]
  have hν :
      (∑ ρ, connection ρ direction ν * (first + second) μ ρ) =
        (∑ ρ, connection ρ direction ν * first μ ρ) +
          ∑ ρ, connection ρ direction ν * second μ ρ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    simp [mul_add]
  unfold covariantDerivative
  rw [map_add, hμ, hν]
  simp only [Pi.add_apply]
  ring

theorem covariantDerivative_smul (connection : Connection) (partialOp : PartialOperator)
    (scalar : ℝ) (tensor : Metric) :
    covariantDerivative connection partialOp (scalar • tensor) =
      scalar • covariantDerivative connection partialOp tensor := by
  funext direction μ ν
  have hμ :
      (∑ ρ, connection ρ direction μ * (scalar • tensor) ρ ν) =
        scalar * ∑ ρ, connection ρ direction μ * tensor ρ ν := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    simp
    ring
  have hν :
      (∑ ρ, connection ρ direction ν * (scalar • tensor) μ ρ) =
        scalar * ∑ ρ, connection ρ direction ν * tensor μ ρ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    simp
    ring
  unfold covariantDerivative
  rw [map_smul, hμ, hν]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Covariant derivative bundled as a linear operator. -/
def covariantDerivativeLinear (connection : Connection) (partialOp : PartialOperator) :
    Metric →ₗ[ℝ] (Index → Metric) where
  toFun := covariantDerivative connection partialOp
  map_add' := covariantDerivative_add connection partialOp
  map_smul' := covariantDerivative_smul connection partialOp

/-- Contract the derivative index and first tensor index with `g⁻¹`. -/
def divergenceValue (inverseMetric : Metric) (connection : Connection)
    (partialOp : PartialOperator) (tensor : Metric) (ν : Index) : ℝ :=
  ∑ direction, ∑ μ,
    inverseMetric direction μ * covariantDerivative connection partialOp tensor direction μ ν

theorem divergenceValue_add (inverseMetric : Metric) (connection : Connection)
    (partialOp : PartialOperator) (first second : Metric) :
    divergenceValue inverseMetric connection partialOp (first + second) =
      divergenceValue inverseMetric connection partialOp first +
        divergenceValue inverseMetric connection partialOp second := by
  funext ν
  simp [divergenceValue, covariantDerivative_add, Finset.sum_add_distrib,
    mul_add]

theorem divergenceValue_smul (inverseMetric : Metric) (connection : Connection)
    (partialOp : PartialOperator) (scalar : ℝ) (tensor : Metric) :
    divergenceValue inverseMetric connection partialOp (scalar • tensor) =
      scalar • divergenceValue inverseMetric connection partialOp tensor := by
  funext ν
  simp only [divergenceValue, covariantDerivative_smul, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ direction, ∑ μ, inverseMetric direction μ *
        (scalar * covariantDerivative connection partialOp tensor direction μ ν)) =
      ∑ direction, ∑ μ, scalar * (inverseMetric direction μ *
        covariantDerivative connection partialOp tensor direction μ ν) := by
          apply Finset.sum_congr rfl
          intro direction _
          apply Finset.sum_congr rfl
          intro μ _
          ring
    _ = scalar * ∑ direction, ∑ μ, inverseMetric direction μ *
        covariantDerivative connection partialOp tensor direction μ ν := by
          simp_rw [← Finset.mul_sum]

/-- The concrete contracted covariant divergence as the linear operator used by
the conservation theorem. -/
def divergence (inverseMetric : Metric) (connection : Connection)
    (partialOp : PartialOperator) : Conservation.Divergence where
  toFun := divergenceValue inverseMetric connection partialOp
  map_add' := divergenceValue_add inverseMetric connection partialOp
  map_smul' := divergenceValue_smul inverseMetric connection partialOp

/-- Metric compatibility is now the concrete equation `∇g = 0`. -/
def MetricCompatible (connection : Connection) (partialOp : PartialOperator)
    (metric : Metric) : Prop :=
  covariantDerivative connection partialOp metric = 0

theorem metricCompatible_divergence_zero
    (metric inverseMetric : Metric) (connection : Connection)
    (partialOp : PartialOperator)
    (compatible : MetricCompatible connection partialOp metric) :
    divergence inverseMetric connection partialOp metric = 0 := by
  funext ν
  have h : ∀ direction μ,
      covariantDerivative connection partialOp metric direction μ ν = 0 := by
    intro direction μ
    exact congrFun (congrFun (congrFun compatible direction) μ) ν
  simp [divergence, divergenceValue, h]

/-- Zero is the partial derivative operator for constant component fields. -/
def zeroPartial : PartialOperator := 0

theorem flat_constant_covariantDerivative (tensor : Metric) :
    covariantDerivative 0 zeroPartial tensor = 0 := by
  funext direction μ ν
  simp [covariantDerivative, zeroPartial]

theorem flat_constant_divergence (inverseMetric tensor : Metric) :
    divergence inverseMetric 0 zeroPartial tensor = 0 := by
  funext ν
  simp [divergence, divergenceValue, flat_constant_covariantDerivative]

/-- In the flat constant geometry the contracted Bianchi condition is derived,
not assumed: the Einstein tensor has zero concrete divergence. -/
theorem flat_contracted_bianchi (metric inverseMetric : Metric) :
    divergence inverseMetric 0 zeroPartial
      (einsteinTensor metric inverseMetric (riemann 0 0)) = 0 :=
  flat_constant_divergence inverseMetric _

/-- Concrete conservation theorem using the component covariant divergence. -/
theorem stressEnergy_conserved_of_geometry
    (sector : EinsteinSector EinsteinTensor4.Tensor)
    (inverseMetric : Metric) (connection : Connection) (partialOp : PartialOperator)
    (equation : sector.lhs = sector.rhs)
    (contracted_bianchi :
      divergence inverseMetric connection partialOp sector.einstein = 0)
    (metric_compatible : MetricCompatible connection partialOp sector.metric)
    (coupling_nonzero : sector.coupling ≠ 0) :
    divergence inverseMetric connection partialOp sector.stressEnergy = 0 := by
  apply Conservation.stressEnergy_conserved sector
    (divergence inverseMetric connection partialOp) equation contracted_bianchi
  · exact metricCompatible_divergence_zero sector.metric inverseMetric
      connection partialOp metric_compatible
  · exact coupling_nonzero

end PhysicsModel.CovariantDerivative
