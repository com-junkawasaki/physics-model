import PhysicsModel.LorentzScattering

/-! # Four-momentum and axis Lorentz boosts in 3+1 dimensions -/

namespace PhysicsModel.Minkowski4

/-- Contravariant four-momentum `(E,pₓ,pᵧ,p_z)` in units `c = 1`. -/
structure FourMomentum where
  energy : ℝ
  px : ℝ
  py : ℝ
  pz : ℝ

def minkowskiNormSq (p : FourMomentum) : ℝ :=
  p.energy ^ 2 - p.px ^ 2 - p.py ^ 2 - p.pz ^ 2

/-- Embed the longitudinal part in the already checked Lorentz momentum type. -/
def longitudinal (p : FourMomentum) : Lorentz.Momentum :=
  ⟨p.energy, p.px⟩

/-- A boost along the x axis; transverse momentum is untouched. -/
def boostX (boost : Lorentz.Boost) (p : FourMomentum) : FourMomentum where
  energy := (boost.act (longitudinal p)).energy
  px := (boost.act (longitudinal p)).momentum
  py := p.py
  pz := p.pz

@[simp] theorem boostX_py (boost : Lorentz.Boost) (p : FourMomentum) :
    (boostX boost p).py = p.py := rfl

@[simp] theorem boostX_pz (boost : Lorentz.Boost) (p : FourMomentum) :
    (boostX boost p).pz = p.pz := rfl

/-- The full 3+1-dimensional Minkowski norm is invariant under an x boost. -/
theorem minkowskiNormSq_boostX (boost : Lorentz.Boost) (p : FourMomentum) :
    minkowskiNormSq (boostX boost p) = minkowskiNormSq p := by
  have h := Lorentz.massSquared_invariant boost (longitudinal p)
  unfold Lorentz.massSquared longitudinal at h
  unfold minkowskiNormSq boostX
  dsimp [longitudinal]
  rw [h]

theorem mass_shell_preserved (boost : Lorentz.Boost) (p : FourMomentum) (mass : ℝ)
    (onShell : minkowskiNormSq p = mass ^ 2) :
    minkowskiNormSq (boostX boost p) = mass ^ 2 := by
  rw [minkowskiNormSq_boostX, onShell]

/-- The relativistic dispersion relation is therefore frame independent. -/
theorem dispersion_preserved (boost : Lorentz.Boost) (p : FourMomentum) (mass : ℝ)
    (dispersion : p.energy ^ 2 = mass ^ 2 + p.px ^ 2 + p.py ^ 2 + p.pz ^ 2) :
    minkowskiNormSq (boostX boost p) = mass ^ 2 := by
  apply mass_shell_preserved boost p mass
  unfold minkowskiNormSq
  rw [dispersion]
  ring

end PhysicsModel.Minkowski4
