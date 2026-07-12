import PhysicsModel.ConnectionError
import Mathlib.Tactic.Linarith

/-! # Error propagation from connections to Riemann curvature

In four dimensions, the two derivative terms and four-term quadratic
connection contribution yield an explicit componentwise curvature bound.
-/

namespace PhysicsModel.CurvatureError

open scoped BigOperators
open PhysicsModel.Geometry4
open PhysicsModel.ConnectionError

/-- Quadratic `ΓΓ` part of one Riemann component. -/
def quadratic (connection : Connection) (ρ σ μ ν : Index) : ℝ :=
  ∑ k, (connection ρ μ k * connection k ν σ -
    connection ρ ν k * connection k μ σ)

theorem riemann_eq_derivative_add_quadratic
    (connection : Connection) (derivative : ConnectionDerivative) (ρ σ μ ν : Index) :
    riemann connection derivative ρ σ μ ν =
      derivative μ ρ ν σ - derivative ν ρ μ σ + quadratic connection ρ σ μ ν := by
  rfl

/-- One quadratic connection product changes by at most `2 B ε`. -/
theorem connection_product_error (fine coarse : Connection) (ε bound : ℝ)
    (hε : 0 ≤ ε) (hBound : 0 ≤ bound)
    (controlled : ∀ ρ μ ν, |fine ρ μ ν - coarse ρ μ ν| ≤ ε)
    (fineBound : ∀ ρ μ ν, |fine ρ μ ν| ≤ bound)
    (coarseBound : ∀ ρ μ ν, |coarse ρ μ ν| ≤ bound)
    (a b c : Index) (x y z : Index) :
    |fine a b c * fine x y z - coarse a b c * coarse x y z| ≤ 2 * bound * ε := by
  have h := abs_mul_sub_mul_le
    (fine a b c) (fine x y z) (coarse a b c) (coarse x y z)
    ε ε bound bound (controlled a b c) (controlled x y z)
    (fineBound a b c) (coarseBound x y z) hε hBound
  nlinarith

/-- The four-dimensional quadratic curvature term changes by at most `16 B ε`. -/
theorem quadratic_error (fine coarse : Connection) (ε bound : ℝ)
    (hε : 0 ≤ ε) (hBound : 0 ≤ bound)
    (controlled : ∀ ρ μ ν, |fine ρ μ ν - coarse ρ μ ν| ≤ ε)
    (fineBound : ∀ ρ μ ν, |fine ρ μ ν| ≤ bound)
    (coarseBound : ∀ ρ μ ν, |coarse ρ μ ν| ≤ bound)
    (ρ σ μ ν : Index) :
    |quadratic fine ρ σ μ ν - quadratic coarse ρ σ μ ν| ≤ 16 * bound * ε := by
  have hterm : ∀ k,
      |(fine ρ μ k * fine k ν σ - fine ρ ν k * fine k μ σ) -
        (coarse ρ μ k * coarse k ν σ - coarse ρ ν k * coarse k μ σ)| ≤
          4 * bound * ε := by
    intro k
    have h1 := connection_product_error fine coarse ε bound hε hBound controlled
      fineBound coarseBound ρ μ k k ν σ
    have h2 := connection_product_error fine coarse ε bound hε hBound controlled
      fineBound coarseBound ρ ν k k μ σ
    have htriangle := abs_sub
      (fine ρ μ k * fine k ν σ - coarse ρ μ k * coarse k ν σ)
      (fine ρ ν k * fine k μ σ - coarse ρ ν k * coarse k μ σ)
    have heq :
        (fine ρ μ k * fine k ν σ - fine ρ ν k * fine k μ σ) -
            (coarse ρ μ k * coarse k ν σ - coarse ρ ν k * coarse k μ σ) =
          (fine ρ μ k * fine k ν σ - coarse ρ μ k * coarse k ν σ) -
            (fine ρ ν k * fine k μ σ - coarse ρ ν k * coarse k μ σ) := by ring
    rw [heq]
    linarith
  unfold quadratic
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k, ((fine ρ μ k * fine k ν σ - fine ρ ν k * fine k μ σ) -
        (coarse ρ μ k * coarse k ν σ - coarse ρ ν k * coarse k μ σ))| ≤
        ∑ _k : Index, 4 * bound * ε :=
      le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun k _ => hterm k)
    _ = 16 * bound * ε := by simp; ring

/-- Explicit componentwise stability of Riemann curvature under refinement. -/
theorem riemann_component_error
    (fineConnection coarseConnection : Connection)
    (fineDerivative coarseDerivative : ConnectionDerivative)
    (εConnection εDerivative connectionBound : ℝ)
    (hεConnection : 0 ≤ εConnection)
    (hConnectionBound : 0 ≤ connectionBound)
    (connectionError : ∀ ρ μ ν,
      |fineConnection ρ μ ν - coarseConnection ρ μ ν| ≤ εConnection)
    (derivativeError : ∀ direction ρ μ ν,
      |fineDerivative direction ρ μ ν -
        coarseDerivative direction ρ μ ν| ≤ εDerivative)
    (fineConnectionBound : ∀ ρ μ ν, |fineConnection ρ μ ν| ≤ connectionBound)
    (coarseConnectionBound : ∀ ρ μ ν, |coarseConnection ρ μ ν| ≤ connectionBound)
    (ρ σ μ ν : Index) :
    |riemann fineConnection fineDerivative ρ σ μ ν -
      riemann coarseConnection coarseDerivative ρ σ μ ν| ≤
        2 * εDerivative + 16 * connectionBound * εConnection := by
  have hd1 := derivativeError μ ρ ν σ
  have hd2 := derivativeError ν ρ μ σ
  have hdTriangle := abs_sub
    (fineDerivative μ ρ ν σ - coarseDerivative μ ρ ν σ)
    (fineDerivative ν ρ μ σ - coarseDerivative ν ρ μ σ)
  have hd :
      |(fineDerivative μ ρ ν σ - coarseDerivative μ ρ ν σ) -
        (fineDerivative ν ρ μ σ - coarseDerivative ν ρ μ σ)| ≤
          2 * εDerivative := by linarith
  have hq := quadratic_error fineConnection coarseConnection εConnection connectionBound
    hεConnection hConnectionBound connectionError fineConnectionBound coarseConnectionBound ρ σ μ ν
  rw [riemann_eq_derivative_add_quadratic, riemann_eq_derivative_add_quadratic]
  have heq :
      (fineDerivative μ ρ ν σ - fineDerivative ν ρ μ σ + quadratic fineConnection ρ σ μ ν) -
          (coarseDerivative μ ρ ν σ - coarseDerivative ν ρ μ σ + quadratic coarseConnection ρ σ μ ν) =
        ((fineDerivative μ ρ ν σ - coarseDerivative μ ρ ν σ) -
          (fineDerivative ν ρ μ σ - coarseDerivative ν ρ μ σ)) +
          (quadratic fineConnection ρ σ μ ν - quadratic coarseConnection ρ σ μ ν) := by ring
  rw [heq]
  exact le_trans (abs_add _ _) (add_le_add hd hq)

end PhysicsModel.CurvatureError
