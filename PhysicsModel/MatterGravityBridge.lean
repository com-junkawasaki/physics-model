import PhysicsModel.ContinuumLimit
import PhysicsModel.EinsteinLimit

/-! # A checked scalar matter--geometry continuum bridge

This is a minimal effective sector, not four-dimensional tensor GR.  It proves
the complete logical chain on a homogeneous scalar component: dyadic Wilson
refinement converges to Maxwell energy, the microscopic residual vanishes, and
the corresponding effective Einstein-sector equation follows by limit
uniqueness.
-/

namespace PhysicsModel

open Filter
open scoped Topology

namespace MatterGravityBridge

/-- One homogeneous component with geometric response matched to Maxwell energy. -/
noncomputable def scalarSector (field : ℝ) : EinsteinSector ℝ where
  einstein := field ^ 2 / 2
  metric := 0
  stressEnergy := field ^ 2 / 2
  cosmologicalConstant := 0
  coupling := 1

/-- Difference between finite-spacing Wilson energy and continuum matter energy. -/
noncomputable def microscopicResidual (field : ℝ) (n : ℕ) : ℝ :=
  ContinuumLimit.scaledWilsonDensity field ((2 : ℝ)⁻¹ ^ n) - field ^ 2 / 2

theorem microscopicResidual_tendsto_zero (field : ℝ) :
    Tendsto (microscopicResidual field) atTop (𝓝 0) := by
  have h := (ContinuumLimit.dyadic_scaledWilsonDensity_tendsto field).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => field ^ 2 / 2)
      atTop (𝓝 (field ^ 2 / 2)))
  change Tendsto
    (fun n : ℕ => ContinuumLimit.scaledWilsonDensity field ((2 : ℝ)⁻¹ ^ n) -
      field ^ 2 / 2) atTop (𝓝 0)
  simpa using h

@[simp] theorem scalarSector_residual (field : ℝ) :
    (scalarSector field).residual = 0 := by
  simp [scalarSector, EinsteinSector.residual, EinsteinSector.lhs,
    EinsteinSector.rhs]

theorem microscopicResidual_tendsto_sector (field : ℝ) :
    Tendsto (microscopicResidual field) atTop (𝓝 (scalarSector field).residual) := by
  simpa using microscopicResidual_tendsto_zero field

/-- Fully checked chain: Wilson refinement implies the homogeneous effective
geometry--matter equation in this scalar sector. -/
theorem effective_equation_from_wilson_refinement (field : ℝ) :
    (scalarSector field).lhs = (scalarSector field).rhs :=
  EinsteinSector.einstein_from_refinement (scalarSector field)
    (microscopicResidual field)
    (microscopicResidual_tendsto_sector field)
    (microscopicResidual_tendsto_zero field)

theorem effective_equation_explicit (field : ℝ) :
    field ^ 2 / 2 + 0 * 0 = 1 * (field ^ 2 / 2) := by ring

end MatterGravityBridge
end PhysicsModel
