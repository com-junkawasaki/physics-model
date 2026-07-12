import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

/-! # Particles as reproducible modes and resonances -/

namespace PhysicsModel

/-- Operational data of a collective excitation. -/
structure Mode where
  mass : ℝ
  width : ℝ
  width_nonnegative : 0 ≤ width
  reproducible : Prop

namespace Mode

def Stable (mode : Mode) : Prop := mode.width = 0 ∧ mode.reproducible
def Resonant (mode : Mode) : Prop := 0 < mode.width ∧ mode.reproducible

/-- Complex pole `M - i Γ/2`. -/
noncomputable def pole (mode : Mode) : ℂ :=
  (mode.mass : ℂ) - Complex.I * (mode.width / 2 : ℝ)

theorem pole_im (mode : Mode) : mode.pole.im = -(mode.width / 2) := by
  simp [pole]

theorem stable_pole_real {mode : Mode} (h : mode.Stable) : mode.pole.im = 0 := by
  rw [pole_im, h.1]
  norm_num

theorem resonant_pole_below_axis {mode : Mode} (h : mode.Resonant) :
    mode.pole.im < 0 := by
  rw [pole_im]
  exact neg_lt_zero.mpr (div_pos h.1 (by norm_num))

theorem stable_or_resonant (mode : Mode) (reproducible : mode.reproducible) :
    mode.Stable ∨ mode.Resonant := by
  rcases eq_or_lt_of_le mode.width_nonnegative with h | h
  · exact Or.inl ⟨h.symm, reproducible⟩
  · exact Or.inr ⟨h, reproducible⟩

end Mode
end PhysicsModel
