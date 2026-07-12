import PhysicsModel.SpecialUnitary
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Nonabelian lattice connection and covariant transport

The link variable is an actual special-unitary matrix.  Local frames act at
both endpoints.  Matter transport, covariant finite differences, and triangle
holonomy then obey their standard nonabelian covariance laws.
-/

namespace PhysicsModel.NonAbelianGauge

open PhysicsModel.SpecialUnitary

universe u v

variable {Vertex : Type u} {n : Type v} [Fintype n] [DecidableEq n]

abbrev Frame (Vertex : Type u) (n : Type v) [Fintype n] [DecidableEq n] :=
  Vertex → SU n

abbrev LinkField (Vertex : Type u) (n : Type v) [Fintype n] [DecidableEq n] :=
  Vertex → Vertex → SU n

abbrev MatterField (Vertex : Type u) (n : Type v) := Vertex → Multiplet n

/-- Local frame transformation of an oriented nonabelian link. -/
def transformLink (frame : Frame Vertex n) (link : LinkField Vertex n) :
    LinkField Vertex n :=
  fun source target => frame source * link source target * (frame target)⁻¹

/-- Matter in the fundamental representation transforms at its site. -/
def transformMatter (frame : Frame Vertex n) (matter : MatterField Vertex n) :
    MatterField Vertex n :=
  fun site => act (frame site) (matter site)

/-- Parallel transport from target back to source. -/
def transport (link : LinkField Vertex n) (matter : MatterField Vertex n)
    (source target : Vertex) : Multiplet n :=
  act (link source target) (matter target)

/-- Transport is covariant at the source endpoint; the target frame cancels. -/
theorem transport_covariant (frame : Frame Vertex n) (link : LinkField Vertex n)
    (matter : MatterField Vertex n) (source target : Vertex) :
    transport (transformLink frame link) (transformMatter frame matter) source target =
      act (frame source) (transport link matter source target) := by
  simp only [transport, transformLink, transformMatter]
  rw [mul_act, mul_act]
  rw [← mul_act (frame target)⁻¹ (frame target), inv_mul_cancel, one_act]

/-- Discrete covariant difference along one oriented link. -/
def covariantDifference (link : LinkField Vertex n) (matter : MatterField Vertex n)
    (source target : Vertex) : Multiplet n :=
  transport link matter source target - matter source

/-- The covariant finite difference transforms in the source representation. -/
theorem covariantDifference_covariant
    (frame : Frame Vertex n) (link : LinkField Vertex n)
    (matter : MatterField Vertex n) (source target : Vertex) :
    covariantDifference (transformLink frame link) (transformMatter frame matter)
        source target =
      act (frame source) (covariantDifference link matter source target) := by
  unfold covariantDifference
  rw [transport_covariant]
  change act (frame source) (transport link matter source target) -
      act (frame source) (matter source) =
    act (frame source) (transport link matter source target - matter source)
  unfold act
  rw [Matrix.mulVec_sub]

/-- Holonomy around an oriented triangle based at `a`. -/
def triangleHolonomy (link : LinkField Vertex n) (a b c : Vertex) : SU n :=
  link a b * link b c * link c a

/-- Closed nonabelian holonomy transforms by conjugation at its base point. -/
theorem triangleHolonomy_covariant (frame : Frame Vertex n)
    (link : LinkField Vertex n) (a b c : Vertex) :
    triangleHolonomy (transformLink frame link) a b c =
      frame a * triangleHolonomy link a b c * (frame a)⁻¹ := by
  simp only [triangleHolonomy, transformLink]
  group

/-- Flatness (`holonomy = 1`) is independent of the local frame. -/
theorem flatness_gauge_invariant (frame : Frame Vertex n)
    (link : LinkField Vertex n) (a b c : Vertex)
    (flat : triangleHolonomy link a b c = 1) :
    triangleHolonomy (transformLink frame link) a b c = 1 := by
  rw [triangleHolonomy_covariant, flat, mul_one, mul_inv_cancel]

/-- Wilson observable: trace of the closed nonabelian holonomy. -/
def triangleWilson (link : LinkField Vertex n) (a b c : Vertex) : ℂ :=
  Matrix.trace (triangleHolonomy link a b c).1

/-- The trace removes base-point conjugation, giving a gauge-invariant observable. -/
theorem triangleWilson_gauge_invariant (frame : Frame Vertex n)
    (link : LinkField Vertex n) (a b c : Vertex) :
    triangleWilson (transformLink frame link) a b c =
      triangleWilson link a b c := by
  unfold triangleWilson
  rw [triangleHolonomy_covariant]
  change Matrix.trace
      ((frame a).1 * (triangleHolonomy link a b c).1 * ((frame a)⁻¹).1) = _
  rw [Matrix.trace_mul_cycle]
  rw [show ((frame a)⁻¹).1 * (frame a).1 = 1 from (frame a).prop.1.1]
  simp

/-- A positive plaquette action built from the Wilson observable. -/
noncomputable def triangleAction (link : LinkField Vertex n) (a b c : Vertex) : ℝ :=
  Complex.normSq (triangleWilson link a b c)

theorem triangleAction_nonnegative (link : LinkField Vertex n) (a b c : Vertex) :
    0 ≤ triangleAction link a b c := Complex.normSq_nonneg _

theorem triangleAction_gauge_invariant (frame : Frame Vertex n)
    (link : LinkField Vertex n) (a b c : Vertex) :
    triangleAction (transformLink frame link) a b c = triangleAction link a b c := by
  unfold triangleAction
  rw [triangleWilson_gauge_invariant]

end PhysicsModel.NonAbelianGauge
