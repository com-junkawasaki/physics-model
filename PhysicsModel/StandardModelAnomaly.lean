import PhysicsModel.StandardModel
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-! # One-generation Standard Model hypercharge anomaly checks

All fermions are represented as left-handed Weyl fields.  The conjugate
right-handed fields therefore carry opposite hypercharge.  These exact rational
computations verify the gravitational, cubic U(1), SU(2)²U(1), and SU(3)²U(1)
anomaly sums for one generation.
-/

namespace PhysicsModel.StandardModelAnomaly

def qY : ℚ := 1 / 6
def uConjY : ℚ := -2 / 3
def dConjY : ℚ := 1 / 3
def leptonY : ℚ := -1 / 2
def eConjY : ℚ := 1

def gravitational : ℚ :=
  6 * qY + 3 * uConjY + 3 * dConjY + 2 * leptonY + eConjY

def cubicU1 : ℚ :=
  6 * qY ^ 3 + 3 * uConjY ^ 3 + 3 * dConjY ^ 3 +
    2 * leptonY ^ 3 + eConjY ^ 3

def su2SquaredU1 : ℚ := 3 * qY + leptonY
def su3SquaredU1 : ℚ := 2 * qY + uConjY + dConjY

theorem gravitational_cancels : gravitational = 0 := by
  norm_num [gravitational, qY, uConjY, dConjY, leptonY, eConjY]

theorem cubic_u1_cancels : cubicU1 = 0 := by
  norm_num [cubicU1, qY, uConjY, dConjY, leptonY, eConjY]

theorem su2_squared_u1_cancels : su2SquaredU1 = 0 := by
  norm_num [su2SquaredU1, qY, leptonY]

theorem su3_squared_u1_cancels : su3SquaredU1 = 0 := by
  norm_num [su3SquaredU1, qY, uConjY, dConjY]

/-- Three identical anomaly-free generations remain anomaly free. -/
theorem three_generation_cubic_cancels : (3 : ℚ) * cubicU1 = 0 := by
  rw [cubic_u1_cancels, mul_zero]

theorem all_local_hypercharge_anomalies_cancel :
    gravitational = 0 ∧ cubicU1 = 0 ∧
      su2SquaredU1 = 0 ∧ su3SquaredU1 = 0 :=
  ⟨gravitational_cancels, cubic_u1_cancels,
    su2_squared_u1_cancels, su3_squared_u1_cancels⟩

end PhysicsModel.StandardModelAnomaly
