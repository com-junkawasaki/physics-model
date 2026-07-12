import PhysicsModel.NonAbelianGauge
import PhysicsModel.Geometry4
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false

/-! # Nonabelian curvature and the second Bianchi identity

For a homogeneous local connection, curvature is the commutator of connection
components.  Its covariant derivative is another commutator.  The differential
Bianchi identity is then exactly the Jacobi identity of the associative matrix
algebra and is proved without commutativity assumptions.
-/

namespace PhysicsModel.YangMillsBianchi

open PhysicsModel.Geometry4
open PhysicsModel.SpecialUnitary

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

abbrev Algebra (n : Type u) := Matrix n n ℂ
abbrev GaugeConnection (n : Type u) := Index → Algebra n
abbrev GaugeCurvature (n : Type u) := Index → Index → Algebra n

def commutator (first second : Algebra n) : Algebra n :=
  first * second - second * first

theorem commutator_antisymmetric (first second : Algebra n) :
    commutator first second = -commutator second first := by
  unfold commutator
  abel

@[simp] theorem commutator_self (value : Algebra n) : commutator value value = 0 := by
  simp [commutator]

/-- Homogeneous nonabelian field strength `F_{μν}=[A_μ,A_ν]`. -/
def curvature (connection : GaugeConnection n) : GaugeCurvature n :=
  fun μ ν => commutator (connection μ) (connection ν)

theorem curvature_antisymmetric (connection : GaugeConnection n) (μ ν : Index) :
    curvature connection μ ν = -curvature connection ν μ :=
  commutator_antisymmetric _ _

@[simp] theorem curvature_diagonal (connection : GaugeConnection n) (μ : Index) :
    curvature connection μ μ = 0 := commutator_self _

/-- Adjoint covariant derivative `D_λF_{μν}=[A_λ,F_{μν}]`. -/
def covariantCurvatureDerivative (connection : GaugeConnection n)
    (fieldStrength : GaugeCurvature n) (direction μ ν : Index) : Algebra n :=
  commutator (connection direction) (fieldStrength μ ν)

/-- Jacobi identity in the matrix Lie algebra. -/
theorem commutator_jacobi (first second third : Algebra n) :
    commutator first (commutator second third) +
      commutator second (commutator third first) +
      commutator third (commutator first second) = 0 := by
  unfold commutator
  noncomm_ring

/-- Differential/second Bianchi identity for the homogeneous nonabelian connection. -/
theorem second_bianchi (connection : GaugeConnection n)
    (direction μ ν : Index) :
    covariantCurvatureDerivative connection (curvature connection) direction μ ν +
      covariantCurvatureDerivative connection (curvature connection) μ ν direction +
      covariantCurvatureDerivative connection (curvature connection) ν direction μ = 0 := by
  exact commutator_jacobi (connection direction) (connection μ) (connection ν)

/-- Constant local gauge transformation by conjugation. -/
def adjoint (g : SU n) (value : Algebra n) : Algebra n :=
  g.1 * value * (g⁻¹).1

def transformConnection (g : SU n) (connection : GaugeConnection n) :
    GaugeConnection n := fun μ => adjoint g (connection μ)

theorem adjoint_mul (g : SU n) (first second : Algebra n) :
    adjoint g (first * second) = adjoint g first * adjoint g second := by
  unfold adjoint
  have h : (g⁻¹).1 * g.1 = 1 := g.prop.1.1
  symm
  calc
    (g.1 * first * (g⁻¹).1) * (g.1 * second * (g⁻¹).1) =
        g.1 * first * ((g⁻¹).1 * g.1) * second * (g⁻¹).1 := by noncomm_ring
    _ = g.1 * first * 1 * second * (g⁻¹).1 := by rw [h]
    _ = g.1 * (first * second) * (g⁻¹).1 := by noncomm_ring

theorem commutator_adjoint (g : SU n) (first second : Algebra n) :
    commutator (adjoint g first) (adjoint g second) =
      adjoint g (commutator first second) := by
  unfold commutator
  rw [← adjoint_mul, ← adjoint_mul]
  unfold adjoint
  noncomm_ring

/-- Nonabelian curvature transforms covariantly in the adjoint representation. -/
theorem curvature_covariant (g : SU n) (connection : GaugeConnection n) (μ ν : Index) :
    curvature (transformConnection g connection) μ ν =
      adjoint g (curvature connection μ ν) := by
  exact commutator_adjoint g (connection μ) (connection ν)

/-- The Bianchi sum itself transforms covariantly. -/
theorem bianchi_adjoint_zero (g : SU n) (connection : GaugeConnection n)
    (direction μ ν : Index) :
    adjoint g
      (covariantCurvatureDerivative connection (curvature connection) direction μ ν +
       covariantCurvatureDerivative connection (curvature connection) μ ν direction +
       covariantCurvatureDerivative connection (curvature connection) ν direction μ) = 0 := by
  rw [second_bianchi]
  simp [adjoint]

end PhysicsModel.YangMillsBianchi
