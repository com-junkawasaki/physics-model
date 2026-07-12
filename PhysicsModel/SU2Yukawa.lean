import PhysicsModel.SpecialUnitary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # SU(2)-invariant antisymmetric contraction

For determinant-one two-dimensional transformations, the alternating tensor
is invariant.  This supplies the nonabelian contraction used by electroweak
Yukawa interactions.
-/

namespace PhysicsModel.SU2Yukawa

open Matrix
open PhysicsModel.SpecialUnitary

/-- The alternating tensor with `ε₀₁ = 1`. -/
def epsilon : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

@[simp] theorem epsilon_zero_zero : epsilon 0 0 = 0 := rfl
@[simp] theorem epsilon_zero_one : epsilon 0 1 = 1 := rfl
@[simp] theorem epsilon_one_zero : epsilon 1 0 = -1 := rfl
@[simp] theorem epsilon_one_one : epsilon 1 1 = 0 := rfl

/-- The alternating tensor is antisymmetric. -/
theorem epsilon_transpose : epsilonᵀ = -epsilon := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsilon]

/-- Any 2×2 matrix scales `ε` by its determinant. -/
theorem transpose_mul_epsilon_mul (matrix : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixᵀ * epsilon * matrix = matrix.det • epsilon := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [epsilon, Matrix.mul_apply, Matrix.det_fin_two] <;> ring

/-- Determinant one makes `ε` exactly SU(2)-invariant. -/
theorem epsilon_invariant (g : SU2) :
    g.1ᵀ * epsilon * g.1 = epsilon := by
  rw [transpose_mul_epsilon_mul, determinant_one g, one_smul]

/-- Alternating bilinear contraction of two weak doublets. -/
def contract (first second : HiggsDoublet) : ℂ :=
  first ⬝ᵥ epsilon *ᵥ second

theorem contract_alternating (field : HiggsDoublet) : contract field field = 0 := by
  simp [contract, epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem contract_antisymmetric (first second : HiggsDoublet) :
    contract first second = -contract second first := by
  simp [contract, epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The weak-doublet contraction is invariant under simultaneous SU(2) action. -/
theorem contract_invariant (g : SU2) (first second : HiggsDoublet) :
    contract (act g first) (act g second) = contract first second := by
  unfold contract act
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  rw [← Matrix.mul_assoc, epsilon_invariant g]
  exact (Matrix.dotProduct_mulVec first epsilon second).symm

/-- Multiplication by an SU(2)-singlet Yukawa coefficient preserves invariance. -/
theorem yukawa_invariant (coupling singlet : ℂ) (g : SU2)
    (left higgs : HiggsDoublet) :
    coupling * contract (act g left) (act g higgs) * singlet =
      coupling * contract left higgs * singlet := by
  rw [contract_invariant]

/-- SU(2)-doublet Higgs potential built only from the invariant Hermitian radius. -/
noncomputable def doubletPotential (coupling vacuumScale : ℝ)
    (higgs : HiggsDoublet) : ℝ :=
  coupling * Complex.normSq (intensity higgs - (vacuumScale ^ 2 : ℝ))

theorem doubletPotential_nonnegative {coupling : ℝ} (vacuumScale : ℝ)
    (higgs : HiggsDoublet) (coupling_nonnegative : 0 ≤ coupling) :
    0 ≤ doubletPotential coupling vacuumScale higgs :=
  mul_nonneg coupling_nonnegative (Complex.normSq_nonneg _)

/-- The Higgs radial potential is invariant under the full nonabelian SU(2) action. -/
theorem doubletPotential_invariant (coupling vacuumScale : ℝ)
    (g : SU2) (higgs : HiggsDoublet) :
    doubletPotential coupling vacuumScale (act g higgs) =
      doubletPotential coupling vacuumScale higgs := by
  unfold doubletPotential
  rw [intensity_invariant]

end PhysicsModel.SU2Yukawa
