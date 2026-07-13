import PhysicsModel.RelativisticScattering
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite families of general `n → m` scattering processes

The `RelativisticScattering.Process` type already models arbitrary finite
incoming and outgoing particle counts.  This module lifts that to finite
families of processes and proves that conservation of total four-momentum is
stable under a common Lorentz frame.
-/

namespace PhysicsModel.ManyBodyScattering

open scoped BigOperators
open PhysicsModel.RelativisticScattering
open PhysicsModel.GeneralLorentz4

universe u v w

/-- A finite family of general scattering processes. -/
structure ProcessFamily
    (Index : Type u) [Fintype Index]
    (Incoming : Type v) [Fintype Incoming]
    (Outgoing : Type w) [Fintype Outgoing] where
  process : Index → Process Incoming Outgoing

namespace ProcessFamily

variable {Index : Type u} {Incoming : Type v} {Outgoing : Type w}
  [Fintype Index] [Fintype Incoming] [Fintype Outgoing]

/-- Total incoming four-momentum of a finite family of processes. -/
def totalIncoming (family : ProcessFamily Index Incoming Outgoing) : SpacetimeVector :=
  ∑ i, totalMomentum (family.process i).incoming

/-- Total outgoing four-momentum of a finite family of processes. -/
def totalOutgoing (family : ProcessFamily Index Incoming Outgoing) : SpacetimeVector :=
  ∑ i, totalMomentum (family.process i).outgoing

/-- Each process conserves momentum, so the whole family does too. -/
theorem totalMomentum_conserved (family : ProcessFamily Index Incoming Outgoing) :
    totalIncoming family = totalOutgoing family := by
  unfold totalIncoming totalOutgoing
  exact Finset.sum_congr rfl fun i hi => (family.process i).conserves

/-- A common Lorentz frame acts pointwise on a finite family of processes. -/
def transform (family : ProcessFamily Index Incoming Outgoing)
    (lorentz : Transform) : ProcessFamily Index Incoming Outgoing where
  process := fun i => (family.process i).transform lorentz

/-- The family total incoming momentum transforms covariantly. -/
theorem totalIncoming_transform
    (family : ProcessFamily Index Incoming Outgoing) (lorentz : Transform) :
    totalIncoming (family.transform lorentz) = lorentz (totalIncoming family) := by
  unfold totalIncoming transform
  simpa [Process.transform, RelativisticScattering.totalMomentum_transform] using
    (map_sum lorentz.toLinearEquiv
      (fun i => totalMomentum (family.process i).incoming) Finset.univ).symm

/-- The family total outgoing momentum transforms covariantly. -/
theorem totalOutgoing_transform
    (family : ProcessFamily Index Incoming Outgoing) (lorentz : Transform) :
    totalOutgoing (family.transform lorentz) = lorentz (totalOutgoing family) := by
  unfold totalOutgoing transform
  simpa [Process.transform, RelativisticScattering.totalMomentum_transform] using
    (map_sum lorentz.toLinearEquiv
      (fun i => totalMomentum (family.process i).outgoing) Finset.univ).symm

/-- The family-level transformed process is still momentum conserving. -/
theorem transform_preserves_conservation
    (family : ProcessFamily Index Incoming Outgoing) (lorentz : Transform) :
    totalIncoming (family.transform lorentz) = totalOutgoing (family.transform lorentz) := by
  rw [totalIncoming_transform, totalOutgoing_transform, totalMomentum_conserved]

end ProcessFamily

end PhysicsModel.ManyBodyScattering
