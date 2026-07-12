import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import PhysicsModel.ElectroweakCharges

/-! # Concrete SU(2) and SU(3) fundamental actions

Mathlib's `specialUnitaryGroup` supplies actual complex unitary matrices with
determinant one.  This module proves that their fundamental matrix action
composes correctly and preserves the Hermitian quadratic form.
-/

namespace PhysicsModel.SpecialUnitary

open Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

abbrev SU (n : Type u) [Fintype n] [DecidableEq n] :=
  Matrix.specialUnitaryGroup n ℂ

abbrev Multiplet (n : Type u) := n → ℂ

def act (g : SU n) (field : Multiplet n) : Multiplet n := g.1 *ᵥ field

@[simp] theorem one_act (field : Multiplet n) : act (1 : SU n) field = field := by
  simp [act]

theorem mul_act (first second : SU n) (field : Multiplet n) :
    act (first * second) field = act first (act second field) := by
  simp [act, Matrix.mulVec_mulVec]

/-- Hermitian intensity `ψ†ψ`. -/
def intensity (field : Multiplet n) : ℂ := star field ⬝ᵥ field

/-- Special-unitary transformations preserve the fundamental Hermitian form. -/
theorem intensity_invariant (g : SU n) (field : Multiplet n) :
    intensity (act g field) = intensity field := by
  unfold intensity act
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  change star field ᵥ* (star g.1 * g.1) ⬝ᵥ field = star field ⬝ᵥ field
  rw [g.prop.1.1, Matrix.vecMul_one]

/-- Every transformation has determinant one, not merely unit modulus. -/
theorem determinant_one (g : SU n) : g.1.det = 1 := g.prop.2

abbrev HiggsDoublet := Multiplet (Fin 2)
abbrev ColorTriplet := Multiplet (Fin 3)
abbrev SU2 := SU (Fin 2)
abbrev SU3 := SU (Fin 3)

theorem higgs_doublet_norm_invariant (g : SU2) (higgs : HiggsDoublet) :
    intensity (act g higgs) = intensity higgs := intensity_invariant g higgs

theorem color_triplet_norm_invariant (g : SU3) (quark : ColorTriplet) :
    intensity (act g quark) = intensity quark := intensity_invariant g quark

/-- The quadratic kinetic/mass density built from a real coefficient is gauge invariant. -/
noncomputable def quadraticDensity (coefficient : ℝ) (field : Multiplet n) : ℂ :=
  (coefficient : ℂ) * intensity field

theorem quadraticDensity_invariant (coefficient : ℝ) (g : SU n)
    (field : Multiplet n) :
    quadraticDensity coefficient (act g field) = quadraticDensity coefficient field := by
  rw [quadraticDensity, quadraticDensity, intensity_invariant]

/-- Color acts on the first index of a quark weak doublet. -/
def colorAct (color : SU3) (field : Fin 3 → Fin 2 → ℂ) : Fin 3 → Fin 2 → ℂ :=
  fun i a => ∑ j, color.1 i j * field j a

/-- Weak isospin acts independently on the second index. -/
def weakAct (weak : SU2) (field : Fin 3 → Fin 2 → ℂ) : Fin 3 → Fin 2 → ℂ :=
  fun i a => ∑ b, weak.1 a b * field i b

/-- The SU(3) and SU(2) factors commute because they act on independent tensor indices. -/
theorem color_weak_commute (color : SU3) (weak : SU2)
    (field : Fin 3 → Fin 2 → ℂ) :
    colorAct color (weakAct weak field) = weakAct weak (colorAct color field) := by
  funext i a
  simp only [colorAct, weakAct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Combined nonabelian action on the `(3,2)` quark multiplet. -/
def productAct (color : SU3) (weak : SU2)
    (field : Fin 3 → Fin 2 → ℂ) : Fin 3 → Fin 2 → ℂ :=
  colorAct color (weakAct weak field)

end PhysicsModel.SpecialUnitary
