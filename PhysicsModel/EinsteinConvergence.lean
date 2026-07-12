import PhysicsModel.EinsteinError
import Mathlib.Analysis.Normed.Group.Constructions

/-! # Closing the refinement-to-Einstein convergence argument

Uniform control of all sixteen residual components controls the finite tensor
norm.  Vanishing refinement error therefore supplies the coarse-limit premise
of `EinsteinSector.einstein_from_refinement`.
-/

namespace PhysicsModel.EinsteinConvergence

open Filter
open scoped Topology
open PhysicsModel.Geometry4

/-- A uniform component bound controls the supremum norm of a four-tensor. -/
theorem tensor_norm_le_of_component_bound (tensor : Metric) (bound : ℝ)
    (controlled : ∀ μ ν, |tensor μ ν| ≤ bound) :
    ‖tensor‖ ≤ bound := by
  have hbound : 0 ≤ bound := le_trans (abs_nonneg (tensor 0 0)) (controlled 0 0)
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro μ
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro ν
  simpa [Real.norm_eq_abs] using controlled μ ν

/-- Componentwise refinement error tending uniformly to zero gives tensor convergence. -/
theorem tensor_tendsto_of_component_error (fine : ℕ → Metric) (coarse : Metric)
    (bound : ℕ → ℝ) (bound_nonnegative : ∀ n, 0 ≤ bound n)
    (controlled : ∀ n μ ν, |fine n μ ν - coarse μ ν| ≤ bound n)
    (boundTends : Tendsto bound atTop (nhds 0)) :
    Tendsto fine atTop (nhds coarse) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply PhysicsModel.EinsteinSector.residual_tendsto_zero_of_norm
    (fun n => fine n - coarse) bound bound_nonnegative
  · intro n
    apply tensor_norm_le_of_component_bound
    intro μ ν
    simpa using controlled n μ ν
  · exact boundTends

/-- Uniform component convergence plus microscopic residual disappearance proves
all sixteen effective Einstein equations in the coarse sector. -/
theorem einstein_from_component_refinement
    (sector : PhysicsModel.EinsteinSector Metric) (microscopicResidual : ℕ → Metric)
    (bound : ℕ → ℝ) (bound_nonnegative : ∀ n, 0 ≤ bound n)
    (componentControlled : ∀ n μ ν,
      |microscopicResidual n μ ν - sector.residual μ ν| ≤ bound n)
    (boundTends : Tendsto bound atTop (nhds 0))
    (microscopicVanishes : Tendsto microscopicResidual atTop (nhds 0)) :
    sector.lhs = sector.rhs := by
  apply sector.einstein_from_refinement microscopicResidual
  · exact tensor_tendsto_of_component_error microscopicResidual sector.residual
      bound bound_nonnegative componentControlled boundTends
  · exact microscopicVanishes

/-- Tensor equality from refinement entails every component field equation. -/
theorem component_equations_from_refinement
    (sector : PhysicsModel.EinsteinSector Metric) (microscopicResidual : ℕ → Metric)
    (bound : ℕ → ℝ) (bound_nonnegative : ∀ n, 0 ≤ bound n)
    (componentControlled : ∀ n μ ν,
      |microscopicResidual n μ ν - sector.residual μ ν| ≤ bound n)
    (boundTends : Tendsto bound atTop (nhds 0))
    (microscopicVanishes : Tendsto microscopicResidual atTop (nhds 0)) :
    ∀ μ ν,
      sector.einstein μ ν + sector.cosmologicalConstant * sector.metric μ ν =
        sector.coupling * sector.stressEnergy μ ν := by
  exact PhysicsModel.EinsteinTensor4.component_equations_of_tensor_equation sector
    (einstein_from_component_refinement sector microscopicResidual bound bound_nonnegative
      componentControlled boundTends microscopicVanishes)

end PhysicsModel.EinsteinConvergence
