import PhysicsModel.EffectiveGR
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! # From microscopic residual convergence to Einstein dynamics -/

namespace PhysicsModel

open Filter
open scoped Topology

universe u

namespace EinsteinSector

variable {Tensor : Type u} [NormedAddCommGroup Tensor] [NormedSpace ℝ Tensor]

/-- A refinement sequence has both a computed macroscopic limit and vanishing
microscopic equation error.  Uniqueness of limits then forces Einstein's equation. -/
theorem einstein_from_refinement
    (sector : EinsteinSector Tensor) (microscopicResidual : ℕ → Tensor)
    (coarse_limit : Tendsto microscopicResidual atTop (𝓝 sector.residual))
    (vanishing_error : Tendsto microscopicResidual atTop (𝓝 0)) :
    sector.lhs = sector.rhs := by
  have hz : sector.residual = 0 := tendsto_nhds_unique coarse_limit vanishing_error
  exact sector.einstein_from_zero_residual hz

/-- Quantitative residual bounds tending to zero imply the vanishing-error premise. -/
theorem residual_tendsto_zero_of_norm
    (microscopicResidual : ℕ → Tensor)
    (bound : ℕ → ℝ)
    (bound_nonnegative : ∀ n, 0 ≤ bound n)
    (controlled : ∀ n, ‖microscopicResidual n‖ ≤ bound n)
    (bound_tends_zero : Tendsto bound atTop (𝓝 0)) :
    Tendsto microscopicResidual atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at bound_tends_zero
  obtain ⟨N, hN⟩ := bound_tends_zero ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (bound_nonnegative n)] at hb
  simpa [dist_eq_norm] using lt_of_le_of_lt (controlled n) hb

end EinsteinSector
end PhysicsModel
