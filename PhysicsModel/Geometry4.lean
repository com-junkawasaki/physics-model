import PhysicsModel.EinsteinTensor4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! # Four-dimensional connection, curvature, and Einstein tensor

All indices range over `Fin 4`.  Derivatives of connection coefficients are
primitive local data, allowing the algebraic curvature identities and tensor
contractions to be checked without assuming a background coordinate manifold.
-/

namespace PhysicsModel.Geometry4

open scoped BigOperators

abbrev Index := Fin 4
abbrev Metric := Index → Index → ℝ
abbrev Connection := Index → Index → Index → ℝ
abbrev ConnectionDerivative := Index → Index → Index → Index → ℝ
abbrev RiemannTensor := Index → Index → Index → Index → ℝ

/-- `∂_μ Γ^ρ_{νσ}` is stored as `derivative μ ρ ν σ`. -/
def riemann (connection : Connection) (derivative : ConnectionDerivative) :
    RiemannTensor :=
  fun ρ σ μ ν =>
    derivative μ ρ ν σ - derivative ν ρ μ σ +
      ∑ k, (connection ρ μ k * connection k ν σ -
        connection ρ ν k * connection k μ σ)

/-- Riemann curvature is antisymmetric in its last two indices by construction. -/
theorem riemann_swap_last (connection : Connection) (derivative : ConnectionDerivative)
    (ρ σ μ ν : Index) :
    riemann connection derivative ρ σ μ ν =
      -riemann connection derivative ρ σ ν μ := by
  unfold riemann
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

theorem riemann_self_last (connection : Connection) (derivative : ConnectionDerivative)
    (ρ σ μ : Index) : riemann connection derivative ρ σ μ μ = 0 := by
  simp [riemann]

/-- A vanishing connection with vanishing derivative has zero curvature. -/
theorem riemann_zero : riemann (0 : Connection) (0 : ConnectionDerivative) = 0 := by
  funext ρ σ μ ν
  simp [riemann]

/-- Vanishing torsion: symmetry of the two lower connection indices. -/
def TorsionFree (connection : Connection) : Prop :=
  ∀ ρ μ ν, connection ρ μ ν = connection ρ ν μ

/-- Derivatives preserve the lower-index symmetry of a torsion-free connection. -/
def DerivativeTorsionFree (derivative : ConnectionDerivative) : Prop :=
  ∀ direction ρ μ ν, derivative direction ρ μ ν = derivative direction ρ ν μ

/-- First algebraic Bianchi identity for a torsion-free connection. -/
theorem first_bianchi (connection : Connection) (derivative : ConnectionDerivative)
    (hconnection : TorsionFree connection)
    (hderivative : DerivativeTorsionFree derivative)
    (ρ σ μ ν : Index) :
    riemann connection derivative ρ σ μ ν +
      riemann connection derivative ρ μ ν σ +
      riemann connection derivative ρ ν σ μ = 0 := by
  have hBC :
      (∑ k, connection ρ ν k * connection k σ μ) =
        ∑ k, connection ρ ν k * connection k μ σ := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hconnection k σ μ]
  have hDE :
      (∑ k, connection ρ σ k * connection k μ ν) =
        ∑ k, connection ρ σ k * connection k ν μ := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hconnection k μ ν]
  have hFA :
      (∑ k, connection ρ μ k * connection k σ ν) =
        ∑ k, connection ρ μ k * connection k ν σ := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hconnection k σ ν]
  unfold riemann
  simp_rw [Finset.sum_sub_distrib]
  rw [hderivative μ ρ ν σ, hderivative ν ρ σ μ,
    hderivative σ ρ μ ν, hBC, hDE, hFA]
  ring

/-- Ricci contraction `R_{σν} = R^ρ_{ σ ρ ν}`. -/
def ricci (curvature : RiemannTensor) : Metric :=
  fun σ ν => ∑ ρ, curvature ρ σ ρ ν

@[simp] theorem ricci_zero : ricci (0 : RiemannTensor) = 0 := by
  funext σ ν
  simp [ricci]

/-- Scalar curvature obtained with a supplied inverse metric. -/
def scalarCurvature (inverseMetric : Metric) (ricciTensor : Metric) : ℝ :=
  ∑ μ, ∑ ν, inverseMetric μ ν * ricciTensor μ ν

@[simp] theorem scalarCurvature_zero_right (inverseMetric : Metric) :
    scalarCurvature inverseMetric 0 = 0 := by
  simp [scalarCurvature]

/-- Covariant Einstein tensor `G_{μν} = R_{μν} - 1/2 R g_{μν}`. -/
noncomputable def einsteinTensor (metric inverseMetric : Metric)
    (curvature : RiemannTensor) : Metric :=
  fun μ ν =>
    ricci curvature μ ν -
      (1 / 2 : ℝ) * scalarCurvature inverseMetric (ricci curvature) * metric μ ν

@[simp] theorem einsteinTensor_zero_curvature (metric inverseMetric : Metric) :
    einsteinTensor metric inverseMetric 0 = 0 := by
  funext μ ν
  simp [einsteinTensor]

/-- Geometry-derived Einstein sector, with matter and constants supplied explicitly. -/
noncomputable def sector (metric inverseMetric : Metric)
    (connection : Connection) (derivative : ConnectionDerivative)
    (stressEnergy : Metric) (cosmologicalConstant coupling : ℝ) :
    EinsteinSector EinsteinTensor4.Tensor where
  einstein := einsteinTensor metric inverseMetric (riemann connection derivative)
  metric := metric
  stressEnergy := stressEnergy
  cosmologicalConstant := cosmologicalConstant
  coupling := coupling

/-- Flat geometry with zero cosmological constant and zero stress-energy has zero residual. -/
theorem flat_vacuum_residual (metric inverseMetric : Metric) (coupling : ℝ) :
    (sector metric inverseMetric 0 0 0 0 coupling).residual = 0 := by
  funext μ ν
  simp [sector, EinsteinSector.residual, EinsteinSector.lhs, EinsteinSector.rhs,
    riemann_zero]

/-- The checked flat vacuum satisfies all sixteen effective Einstein equations. -/
theorem flat_vacuum_equations (metric inverseMetric : Metric) (coupling : ℝ) :
    ∀ μ ν,
      (sector metric inverseMetric 0 0 0 0 coupling).einstein μ ν +
          (sector metric inverseMetric 0 0 0 0 coupling).cosmologicalConstant *
            (sector metric inverseMetric 0 0 0 0 coupling).metric μ ν =
        (sector metric inverseMetric 0 0 0 0 coupling).coupling *
          (sector metric inverseMetric 0 0 0 0 coupling).stressEnergy μ ν := by
  apply EinsteinTensor4.component_equations_of_tensor_equation
  exact EinsteinSector.einstein_from_zero_residual _
    (flat_vacuum_residual metric inverseMetric coupling)

end PhysicsModel.Geometry4
