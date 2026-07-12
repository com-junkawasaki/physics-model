import PhysicsModel.GeneralLorentz4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Lorentz-covariant multiparticle scattering kinematics -/

namespace PhysicsModel.RelativisticScattering

open scoped BigOperators
open PhysicsModel.GeneralLorentz4

universe u v

/-- Total four-momentum of a finite family of particles. -/
def totalMomentum {Particle : Type u} [Fintype Particle]
    (momentum : Particle → SpacetimeVector) : SpacetimeVector :=
  ∑ particle, momentum particle

/-- Apply one common frame change to every particle momentum. -/
def transformMomenta {Particle : Type u} (lorentz : Transform)
    (momentum : Particle → SpacetimeVector) : Particle → SpacetimeVector :=
  fun particle => lorentz (momentum particle)

/-- A linear Lorentz transformation commutes with finite total momentum. -/
theorem totalMomentum_transform {Particle : Type u} [Fintype Particle]
    (lorentz : Transform) (momentum : Particle → SpacetimeVector) :
    totalMomentum (transformMomenta lorentz momentum) = lorentz (totalMomentum momentum) := by
  unfold totalMomentum transformMomenta
  exact (map_sum lorentz.toLinearEquiv momentum Finset.univ).symm

/-- Finite incoming and outgoing particle families with conserved four-momentum. -/
structure Process (Incoming : Type u) (Outgoing : Type v)
    [Fintype Incoming] [Fintype Outgoing] where
  incoming : Incoming → SpacetimeVector
  outgoing : Outgoing → SpacetimeVector
  conserves : totalMomentum incoming = totalMomentum outgoing

namespace Process

variable {Incoming : Type u} {Outgoing : Type v}
  [Fintype Incoming] [Fintype Outgoing]

/-- The same scattering process described in another Lorentz frame. -/
def transform (process : Process Incoming Outgoing) (lorentz : Transform) :
    Process Incoming Outgoing where
  incoming := transformMomenta lorentz process.incoming
  outgoing := transformMomenta lorentz process.outgoing
  conserves := by
    rw [totalMomentum_transform, totalMomentum_transform, process.conserves]

@[simp] theorem transform_incoming (process : Process Incoming Outgoing)
    (lorentz : Transform) (particle : Incoming) :
    (process.transform lorentz).incoming particle = lorentz (process.incoming particle) := rfl

@[simp] theorem transform_outgoing (process : Process Incoming Outgoing)
    (lorentz : Transform) (particle : Outgoing) :
    (process.transform lorentz).outgoing particle = lorentz (process.outgoing particle) := rfl

theorem transform_identity (process : Process Incoming Outgoing) :
    process.transform Transform.identity = process := by
  cases process with
  | mk incoming outgoing conserves => rfl

theorem transform_comp (process : Process Incoming Outgoing)
    (second first : Transform) :
    (process.transform first).transform second = process.transform (Transform.comp second first) := by
  cases process with
  | mk incoming outgoing conserves => rfl

end Process

/-- Labelled kinematics of a `2 → 2` scattering event. -/
structure TwoToTwo where
  p₁ : SpacetimeVector
  p₂ : SpacetimeVector
  p₃ : SpacetimeVector
  p₄ : SpacetimeVector
  conserves : p₁ + p₂ = p₃ + p₄

namespace TwoToTwo

/-- Mandelstam center-of-mass invariant. -/
def s (event : TwoToTwo) : ℝ := normSq (event.p₁ + event.p₂)

/-- Mandelstam momentum-transfer invariant. -/
def t (event : TwoToTwo) : ℝ := normSq (event.p₁ - event.p₃)

/-- Crossed-channel Mandelstam invariant. -/
def u (event : TwoToTwo) : ℝ := normSq (event.p₁ - event.p₄)

/-- Transform all four external legs to a common Lorentz frame. -/
def transform (event : TwoToTwo) (lorentz : Transform) : TwoToTwo where
  p₁ := lorentz event.p₁
  p₂ := lorentz event.p₂
  p₃ := lorentz event.p₃
  p₄ := lorentz event.p₄
  conserves := by
    simpa only [map_add] using congrArg lorentz event.conserves

theorem external_mass_shell_preserved (event : TwoToTwo) (lorentz : Transform)
    (leg : Fin 4) :
    normSq ((![event.p₁, event.p₂, event.p₃, event.p₄] : Fin 4 → SpacetimeVector) leg) =
      normSq ((![(event.transform lorentz).p₁, (event.transform lorentz).p₂,
        (event.transform lorentz).p₃, (event.transform lorentz).p₄] :
          Fin 4 → SpacetimeVector) leg) := by
  fin_cases leg <;> simp [transform, Transform.normSq_invariant]

theorem s_invariant (event : TwoToTwo) (lorentz : Transform) :
    (event.transform lorentz).s = event.s := by
  unfold s transform
  rw [← lorentz.toLinearEquiv.map_add, Transform.normSq_invariant]

theorem t_invariant (event : TwoToTwo) (lorentz : Transform) :
    (event.transform lorentz).t = event.t := by
  unfold t transform
  change normSq (lorentz event.p₁ - lorentz event.p₃) = normSq (event.p₁ - event.p₃)
  have h := map_sub lorentz.toLinearEquiv event.p₁ event.p₃
  rw [h.symm, Transform.normSq_invariant]

theorem u_invariant (event : TwoToTwo) (lorentz : Transform) :
    (event.transform lorentz).u = event.u := by
  unfold u transform
  change normSq (lorentz event.p₁ - lorentz event.p₄) = normSq (event.p₁ - event.p₄)
  have h := map_sub lorentz.toLinearEquiv event.p₁ event.p₄
  rw [h.symm, Transform.normSq_invariant]

/-- Every function of `s,t,u` is automatically a Lorentz-scalar scattering amplitude. -/
theorem invariantAmplitude (amplitude : ℝ → ℝ → ℝ → ℂ)
    (event : TwoToTwo) (lorentz : Transform) :
    amplitude (event.transform lorentz).s (event.transform lorentz).t
      (event.transform lorentz).u = amplitude event.s event.t event.u := by
  rw [s_invariant, t_invariant, u_invariant]

end TwoToTwo

end PhysicsModel.RelativisticScattering
