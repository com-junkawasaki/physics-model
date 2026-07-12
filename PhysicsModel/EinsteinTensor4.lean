import PhysicsModel.EinsteinLimit
import Mathlib.Data.Fin.Basic

/-! # Componentwise four-dimensional effective Einstein equations -/

namespace PhysicsModel.EinsteinTensor4

open Filter
open scoped Topology

/-- A real rank-two tensor with four spacetime indices. -/
abbrev Tensor := Fin 4 → Fin 4 → ℝ

/-- Symmetry appropriate to metric, Einstein, and stress-energy tensors. -/
def Symmetric (tensor : Tensor) : Prop := ∀ μ ν, tensor μ ν = tensor ν μ

theorem zero_symmetric : Symmetric (0 : Tensor) := by
  intro μ ν
  rfl

theorem add_symmetric {first second : Tensor}
    (hfirst : Symmetric first) (hsecond : Symmetric second) :
    Symmetric (first + second) := by
  intro μ ν
  simp only [Pi.add_apply]
  rw [hfirst μ ν, hsecond μ ν]

theorem smul_symmetric (scalar : ℝ) {tensor : Tensor}
    (h : Symmetric tensor) : Symmetric (scalar • tensor) := by
  intro μ ν
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h μ ν]

/-- Equality of effective tensors yields all sixteen component equations. -/
theorem component_equations_of_tensor_equation (sector : EinsteinSector Tensor)
    (equation : sector.lhs = sector.rhs) :
    ∀ μ ν,
      sector.einstein μ ν +
          sector.cosmologicalConstant * sector.metric μ ν =
        sector.coupling * sector.stressEnergy μ ν := by
  intro μ ν
  have h := congrFun (congrFun equation μ) ν
  simpa [EinsteinSector.lhs, EinsteinSector.rhs] using h

/-- A convergent four-tensor refinement with vanishing equation error proves
the effective Einstein equation in every spacetime component. -/
theorem components_from_refinement
    (sector : EinsteinSector Tensor) (microscopicResidual : ℕ → Tensor)
    (coarse_limit : Tendsto microscopicResidual atTop (𝓝 sector.residual))
    (vanishing_error : Tendsto microscopicResidual atTop (𝓝 0)) :
    ∀ μ ν,
      sector.einstein μ ν +
          sector.cosmologicalConstant * sector.metric μ ν =
        sector.coupling * sector.stressEnergy μ ν := by
  apply component_equations_of_tensor_equation sector
  exact EinsteinSector.einstein_from_refinement sector microscopicResidual
    coarse_limit vanishing_error

/-- If the geometric and matter tensors are symmetric, both sides of the
effective field equation retain that tensor symmetry. -/
theorem equation_sides_symmetric (sector : EinsteinSector Tensor)
    (einstein_symmetric : Symmetric sector.einstein)
    (metric_symmetric : Symmetric sector.metric)
    (stress_symmetric : Symmetric sector.stressEnergy) :
    Symmetric sector.lhs ∧ Symmetric sector.rhs := by
  constructor
  · exact add_symmetric einstein_symmetric
      (smul_symmetric sector.cosmologicalConstant metric_symmetric)
  · exact smul_symmetric sector.coupling stress_symmetric

end PhysicsModel.EinsteinTensor4
