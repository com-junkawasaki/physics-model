import PhysicsModel.CoarseGeometry4
import Mathlib.Topology.MetricSpace.Basic

/-! # Quantitative approximate refinement of relational geometry

Nodewise errors in weighted relational correlations control the emergent metric.
This supplies a quantitative bridge from finite graph refinements to componentwise
continuum convergence.
-/

namespace PhysicsModel.ApproximateRefinement

open scoped BigOperators Topology
open Filter
open PhysicsModel.CoarseGeometry4
open PhysicsModel.Geometry4

universe u

variable {Node : Type u} [Fintype Node]

/-- Contribution of one relational node to one coarse metric component. -/
def contribution (chart : RelationalChart Node) (node : Node) (μ ν : Index) : ℝ :=
  chart.weight node * chart.coordinate node μ * chart.coordinate node ν

/-- A nodewise certificate that a fine chart approximates a coarse chart. -/
structure Certificate (coarse fine : RelationalChart Node) where
  error : Node → ℝ
  error_nonnegative : ∀ node, 0 ≤ error node
  controlled : ∀ node μ ν,
    |contribution fine node μ ν - contribution coarse node μ ν| ≤ error node

namespace Certificate

variable {coarse fine : RelationalChart Node}

theorem metric_sub_eq_sum (_certificate : Certificate coarse fine) (μ ν : Index) :
    fine.metric μ ν - coarse.metric μ ν =
      ∑ node, (contribution fine node μ ν - contribution coarse node μ ν) := by
  unfold RelationalChart.metric contribution
  rw [Finset.sum_sub_distrib]

/-- Total nodewise correlation error bounds every emergent metric component. -/
theorem metric_component_error (certificate : Certificate coarse fine) (μ ν : Index) :
    |fine.metric μ ν - coarse.metric μ ν| ≤ ∑ node, certificate.error node := by
  rw [certificate.metric_sub_eq_sum]
  calc
    |∑ node, (contribution fine node μ ν - contribution coarse node μ ν)| ≤
        ∑ node, |contribution fine node μ ν - contribution coarse node μ ν| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ node, certificate.error node := by
      exact Finset.sum_le_sum fun node _ => certificate.controlled node μ ν

/-- A uniform per-node error gives the explicit `card Node · η` metric bound. -/
theorem metric_component_error_uniform (certificate : Certificate coarse fine) (η : ℝ)
    (uniform : ∀ node, certificate.error node ≤ η) (μ ν : Index) :
    |fine.metric μ ν - coarse.metric μ ν| ≤ (Fintype.card Node : ℝ) * η := by
  calc
    |fine.metric μ ν - coarse.metric μ ν| ≤ ∑ node, certificate.error node :=
      certificate.metric_component_error μ ν
    _ ≤ ∑ _node : Node, η := by
      exact Finset.sum_le_sum fun node _ => uniform node
    _ = (Fintype.card Node : ℝ) * η := by simp

end Certificate

/-- Vanishing total refinement error implies convergence of every metric component. -/
theorem metric_component_tendsto (coarse : RelationalChart Node)
    (fine : ℕ → RelationalChart Node)
    (certificate : ∀ n, Certificate coarse (fine n))
    (errorTends : Tendsto (fun n => ∑ node, (certificate n).error node) atTop (nhds 0))
    (μ ν : Index) :
    Tendsto (fun n => (fine n).metric μ ν) atTop (nhds (coarse.metric μ ν)) := by
  rw [Metric.tendsto_atTop]
  rw [Metric.tendsto_atTop] at errorTends
  intro ε hε
  obtain ⟨N, hN⟩ := errorTends ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hTotalNonnegative : 0 ≤ ∑ node, (certificate n).error node := by
    exact Finset.sum_nonneg fun node _ => (certificate n).error_nonnegative node
  have hTotal : (∑ node, (certificate n).error node) < ε := by
    simpa [Real.dist_eq, abs_of_nonneg hTotalNonnegative] using hN n hn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt ((certificate n).metric_component_error μ ν) hTotal

end PhysicsModel.ApproximateRefinement
