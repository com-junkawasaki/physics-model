import PhysicsModel.ElectroweakBreaking
import Mathlib.Tactic.Module

/-! # Chiral projectors from an involutive gamma-five operator -/

namespace PhysicsModel.Chirality

universe u

variable (Spinor : Type u) [AddCommGroup Spinor] [Module ℂ Spinor]

/-- Abstract gamma-five data; the Clifford-algebra consequence `γ⁵²=1` is explicit. -/
structure Operator where
  gammaFive : Spinor →ₗ[ℂ] Spinor
  involutive : gammaFive.comp gammaFive = LinearMap.id

namespace Operator

variable {Spinor : Type u} [AddCommGroup Spinor] [Module ℂ Spinor]

noncomputable def left (operator : Operator Spinor) (spinor : Spinor) : Spinor :=
  (1 / 2 : ℂ) • (spinor - operator.gammaFive spinor)

noncomputable def right (operator : Operator Spinor) (spinor : Spinor) : Spinor :=
  (1 / 2 : ℂ) • (spinor + operator.gammaFive spinor)

theorem gammaFive_involutive (operator : Operator Spinor) (spinor : Spinor) :
    operator.gammaFive (operator.gammaFive spinor) = spinor := by
  have h := LinearMap.congr_fun operator.involutive spinor
  simpa using h

/-- Left and right components reconstruct every spinor. -/
theorem left_add_right (operator : Operator Spinor) (spinor : Spinor) :
    operator.left spinor + operator.right spinor = spinor := by
  unfold left right
  module

/-- The left projector is idempotent. -/
theorem left_idempotent (operator : Operator Spinor) (spinor : Spinor) :
    operator.left (operator.left spinor) = operator.left spinor := by
  unfold left
  rw [map_smul, map_sub, operator.gammaFive_involutive]
  module

/-- The right projector is idempotent. -/
theorem right_idempotent (operator : Operator Spinor) (spinor : Spinor) :
    operator.right (operator.right spinor) = operator.right spinor := by
  unfold right
  rw [map_smul, map_add, operator.gammaFive_involutive]
  module

/-- The right projector annihilates a left-handed spinor. -/
theorem right_left_zero (operator : Operator Spinor) (spinor : Spinor) :
    operator.right (operator.left spinor) = 0 := by
  unfold right left
  rw [map_smul, map_sub, operator.gammaFive_involutive]
  module

/-- The left projector annihilates a right-handed spinor. -/
theorem left_right_zero (operator : Operator Spinor) (spinor : Spinor) :
    operator.left (operator.right spinor) = 0 := by
  unfold left right
  rw [map_smul, map_add, operator.gammaFive_involutive]
  module

/-- Left-handed components have gamma-five eigenvalue `-1`. -/
theorem gammaFive_left (operator : Operator Spinor) (spinor : Spinor) :
    operator.gammaFive (operator.left spinor) = -operator.left spinor := by
  unfold left
  rw [map_smul, map_sub, operator.gammaFive_involutive]
  module

/-- Right-handed components have gamma-five eigenvalue `+1`. -/
theorem gammaFive_right (operator : Operator Spinor) (spinor : Spinor) :
    operator.gammaFive (operator.right spinor) = operator.right spinor := by
  unfold right
  rw [map_smul, map_add, operator.gammaFive_involutive]
  module

/-- A spinor fixed by gamma-five is purely right handed. -/
theorem right_of_positive_chirality (operator : Operator Spinor) (spinor : Spinor)
    (positive : operator.gammaFive spinor = spinor) :
    operator.right spinor = spinor ∧ operator.left spinor = 0 := by
  constructor
  · unfold right
    rw [positive]
    module
  · unfold left
    rw [positive]
    module

/-- A spinor negated by gamma-five is purely left handed. -/
theorem left_of_negative_chirality (operator : Operator Spinor) (spinor : Spinor)
    (negative : operator.gammaFive spinor = -spinor) :
    operator.left spinor = spinor ∧ operator.right spinor = 0 := by
  constructor
  · unfold left
    rw [negative]
    module
  · unfold right
    rw [negative]
    module

end Operator

end PhysicsModel.Chirality
