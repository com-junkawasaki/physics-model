import PhysicsModel.SecondBianchi4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Contracted Bianchi identity in four-dimensional normal coordinates

At a point in orthonormal normal coordinates, raising/lowering is represented by
Kronecker contraction.  The differential Bianchi identity and standard Riemann
pair symmetries imply `div Ricci = 1/2 grad scalar`, hence `div Einstein = 0`.
-/

namespace PhysicsModel.ContractedBianchi4

open scoped BigOperators
open PhysicsModel.Geometry4

/-- `D κ a b c d = ∇_κ R_{abcd}` at the selected normal-coordinate point. -/
abbrev CurvatureDerivative := Index → Index → Index → Index → Index → ℝ

structure RiemannDerivativeLaws (D : CurvatureDerivative) : Prop where
  antisymFirst : ∀ κ a b c d, D κ a b c d = -D κ b a c d
  antisymLast : ∀ κ a b c d, D κ a b c d = -D κ a b d c
  pairExchange : ∀ κ a b c d, D κ a b c d = D κ c d a b
  secondBianchi : ∀ e a b c d,
    D e a b c d + D c a b d e + D d a b e c = 0

/-- Derivative of Ricci: `∇_κ R_{bd} = Σ_a ∇_κ R_{abad}`. -/
def ricciDerivative (D : CurvatureDerivative) (κ b d : Index) : ℝ :=
  ∑ a, D κ a b a d

/-- Derivative of scalar curvature in orthonormal normal coordinates. -/
def scalarDerivative (D : CurvatureDerivative) (κ : Index) : ℝ :=
  ∑ b, ricciDerivative D κ b b

/-- Divergence of Ricci. -/
def ricciDivergence (D : CurvatureDerivative) (ν : Index) : ℝ :=
  ∑ μ, ricciDerivative D μ μ ν

/-- First contraction of differential Bianchi. -/
theorem first_contraction {D : CurvatureDerivative} (laws : RiemannDerivativeLaws D)
    (b d e : Index) :
    (∑ a, D a a b d e) =
      ricciDerivative D d b e - ricciDerivative D e b d := by
  have hzero :
      (∑ a, (D e a b a d + D a a b d e + D d a b e a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact laws.secondBianchi e a b a d
  simp_rw [Finset.sum_add_distrib] at hzero
  have hfirst : (∑ a, D e a b a d) = ricciDerivative D e b d := rfl
  have hthird : (∑ a, D d a b e a) = -ricciDerivative D d b e := by
    calc
      (∑ a, D d a b e a) = ∑ a, -D d a b a e := by
        apply Finset.sum_congr rfl
        intro a _
        exact laws.antisymLast d a b e a
      _ = -∑ a, D d a b a e := by rw [Finset.sum_neg_distrib]
      _ = -ricciDerivative D d b e := rfl
  rw [hfirst, hthird] at hzero
  linarith

/-- Double contraction of Riemann's first antisymmetric pair. -/
theorem double_contraction_left {D : CurvatureDerivative}
    (laws : RiemannDerivativeLaws D) (e : Index) :
    (∑ b, ∑ a, D a a b b e) = -ricciDivergence D e := by
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ b, D a a b b e) = ∑ a, ∑ b, -D a b a b e := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact laws.antisymFirst a a b b e
    _ = ∑ a, -(∑ b, D a b a b e) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_neg_distrib]
    _ = -∑ a, ricciDerivative D a a e := by
      rw [Finset.sum_neg_distrib]
      congr 1
    _ = -ricciDivergence D e := rfl

/-- Contracted Bianchi identity `∇^μR_{μν}=1/2 ∇_νR`. -/
theorem contracted_bianchi_ricci {D : CurvatureDerivative}
    (laws : RiemannDerivativeLaws D) (e : Index) :
    ricciDivergence D e = (1 / 2 : ℝ) * scalarDerivative D e := by
  have hall :
      (∑ b, ∑ a, D a a b b e) =
        (∑ b, ricciDerivative D b b e) -
          ∑ b, ricciDerivative D e b b := by
    calc
      (∑ b, ∑ a, D a a b b e) =
          ∑ b, (ricciDerivative D b b e - ricciDerivative D e b b) := by
        apply Finset.sum_congr rfl
        intro b _
        exact first_contraction laws b b e
      _ = (∑ b, ricciDerivative D b b e) -
          ∑ b, ricciDerivative D e b b := by
        rw [Finset.sum_sub_distrib]
  rw [double_contraction_left laws] at hall
  change -ricciDivergence D e =
    ricciDivergence D e - scalarDerivative D e at hall
  linarith

/-- Normal-coordinate derivative of Einstein tensor. -/
noncomputable def einsteinDerivative (D : CurvatureDerivative) (κ μ ν : Index) : ℝ :=
  ricciDerivative D κ μ ν -
    (1 / 2 : ℝ) * scalarDerivative D κ * if μ = ν then 1 else 0

noncomputable def einsteinDivergence (D : CurvatureDerivative) (ν : Index) : ℝ :=
  ∑ μ, einsteinDerivative D μ μ ν

/-- Contracted Bianchi identity `∇^μG_{μν}=0`. -/
theorem contracted_bianchi_einstein {D : CurvatureDerivative}
    (laws : RiemannDerivativeLaws D) (ν : Index) :
    einsteinDivergence D ν = 0 := by
  unfold einsteinDivergence einsteinDerivative
  rw [show (∑ μ, (ricciDerivative D μ μ ν -
      (1 / 2 : ℝ) * scalarDerivative D μ * if μ = ν then 1 else 0)) =
      (∑ μ, ricciDerivative D μ μ ν) -
        (1 / 2 : ℝ) * scalarDerivative D ν by
    rw [Finset.sum_sub_distrib]
    congr 1
    simp]
  change ricciDivergence D ν - (1 / 2 : ℝ) * scalarDerivative D ν = 0
  rw [contracted_bianchi_ricci laws]
  ring

/-- Derivative data for any covariant rank-two tensor. -/
abbrev TensorDerivative := Index → Index → Index → ℝ

def tensorDivergence (derivative : TensorDerivative) (ν : Index) : ℝ :=
  ∑ μ, derivative μ μ ν

theorem einstein_tensorDivergence_zero {D : CurvatureDerivative}
    (laws : RiemannDerivativeLaws D) :
    tensorDivergence (einsteinDerivative D) = 0 := by
  funext ν
  exact contracted_bianchi_einstein laws ν

/-- Differentiated Einstein equation plus contracted Bianchi implies local
stress-energy conservation at the normal-coordinate point. -/
theorem stressEnergy_conserved
    {D : CurvatureDerivative} (laws : RiemannDerivativeLaws D)
    (stressDerivative : TensorDerivative) (coupling : ℝ)
    (coupling_nonzero : coupling ≠ 0)
    (differentiatedEinstein : ∀ κ μ ν,
      einsteinDerivative D κ μ ν = coupling * stressDerivative κ μ ν) :
    tensorDivergence stressDerivative = 0 := by
  funext ν
  have hzero := contracted_bianchi_einstein laws ν
  unfold einsteinDivergence at hzero
  simp_rw [differentiatedEinstein] at hzero
  rw [← Finset.mul_sum] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left coupling_nonzero

end PhysicsModel.ContractedBianchi4
