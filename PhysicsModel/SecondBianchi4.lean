import PhysicsModel.Geometry4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! # Four-dimensional differential Bianchi identity in normal coordinates

The covariant derivative of a `(1,3)` Riemann tensor is defined with all four
connection terms.  At any chosen point, normal coordinates set `Γ=0`; there the
derivative of curvature is expressed through second derivatives of `Γ`.
Commutation of partial derivatives then proves the differential Bianchi identity.
-/

namespace PhysicsModel.SecondBianchi4

open scoped BigOperators
open PhysicsModel.Geometry4

abbrev RiemannPartialDerivative := Index → RiemannTensor

/-- Covariant derivative `∇_κ R^ρ_{ σ μ ν}` of a rank `(1,3)` tensor. -/
def covariantRiemannDerivative (connection : Connection)
    (partialRiemann : RiemannPartialDerivative)
    (curvature : RiemannTensor) (κ ρ σ μ ν : Index) : ℝ :=
  partialRiemann κ ρ σ μ ν +
    (∑ k, connection ρ κ k * curvature k σ μ ν) -
    (∑ k, connection k κ σ * curvature ρ k μ ν) -
    (∑ k, connection k κ μ * curvature ρ σ k ν) -
    ∑ k, connection k κ ν * curvature ρ σ μ k

/-- At a normal-coordinate point (`Γ=0`), covariant and partial derivatives agree. -/
@[simp] theorem covariantRiemannDerivative_zero_connection
    (partialRiemann : RiemannPartialDerivative) (curvature : RiemannTensor)
    (κ ρ σ μ ν : Index) :
    covariantRiemannDerivative 0 partialRiemann curvature κ ρ σ μ ν =
      partialRiemann κ ρ σ μ ν := by
  simp [covariantRiemannDerivative]

/-- `∂_κ∂_μ Γ^ρ_{νσ}`. -/
abbrev SecondConnectionDerivative :=
  Index → Index → Index → Index → Index → ℝ

/-- Commutation of coordinate partial derivatives. -/
def PartialsCommute (second : SecondConnectionDerivative) : Prop :=
  ∀ firstDirection secondDirection ρ ν σ,
    second firstDirection secondDirection ρ ν σ =
      second secondDirection firstDirection ρ ν σ

/-- At a normal-coordinate point, the derivative of Riemann curvature contains
only the antisymmetrized second derivatives of the connection. -/
def normalRiemannDerivative (second : SecondConnectionDerivative) :
    RiemannPartialDerivative :=
  fun κ ρ σ μ ν =>
    second κ μ ρ ν σ - second κ ν ρ μ σ

/-- Normal-coordinate derivative is antisymmetric in the curvature-form indices. -/
theorem normalRiemannDerivative_swap_last (second : SecondConnectionDerivative)
    (κ ρ σ μ ν : Index) :
    normalRiemannDerivative second κ ρ σ μ ν =
      -normalRiemannDerivative second κ ρ σ ν μ := by
  unfold normalRiemannDerivative
  ring

/-- Differential/second Bianchi identity at an arbitrary point expressed in
normal coordinates.  Since the identity is tensorial, this is its local
coordinate calculation. -/
theorem second_bianchi_normal_coordinates
    (second : SecondConnectionDerivative) (commutes : PartialsCommute second)
    (κ ρ σ μ ν : Index) :
    normalRiemannDerivative second κ ρ σ μ ν +
      normalRiemannDerivative second μ ρ σ ν κ +
      normalRiemannDerivative second ν ρ σ κ μ = 0 := by
  unfold normalRiemannDerivative
  rw [commutes κ μ ρ ν σ, commutes μ ν ρ κ σ,
    commutes ν κ ρ μ σ]
  ring

/-- The same identity stated using the full covariant-derivative definition at
the normal-coordinate point. -/
theorem covariant_second_bianchi_at_normal_point
    (second : SecondConnectionDerivative) (commutes : PartialsCommute second)
    (curvature : RiemannTensor) (κ ρ σ μ ν : Index) :
    covariantRiemannDerivative 0 (normalRiemannDerivative second) curvature κ ρ σ μ ν +
      covariantRiemannDerivative 0 (normalRiemannDerivative second) curvature μ ρ σ ν κ +
      covariantRiemannDerivative 0 (normalRiemannDerivative second) curvature ν ρ σ κ μ = 0 := by
  simp only [covariantRiemannDerivative_zero_connection]
  exact second_bianchi_normal_coordinates second commutes κ ρ σ μ ν

/-- Constant connection coefficients have commuting zero second derivatives and
therefore satisfy the differential Bianchi identity. -/
theorem constant_connection_second_bianchi (curvature : RiemannTensor)
    (κ ρ σ μ ν : Index) :
    covariantRiemannDerivative 0 (normalRiemannDerivative 0) curvature κ ρ σ μ ν +
      covariantRiemannDerivative 0 (normalRiemannDerivative 0) curvature μ ρ σ ν κ +
      covariantRiemannDerivative 0 (normalRiemannDerivative 0) curvature ν ρ σ κ μ = 0 := by
  apply covariant_second_bianchi_at_normal_point
  intro firstDirection secondDirection ρ' ν' σ'
  rfl

end PhysicsModel.SecondBianchi4
