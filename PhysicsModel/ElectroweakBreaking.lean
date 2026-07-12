import PhysicsModel.ElectroweakCharges
import PhysicsModel.HiggsMechanism
import Mathlib.Tactic.FieldSimp

/-! # Electroweak symmetry breaking and gauge-boson masses

The neutral Higgs vacuum induces the standard rank-one mass matrix in the
`(W³,B)` basis.  Its kernel is the photon direction and its orthogonal eigenvector
is the massive `Z`.  The charged `W` and neutral `Z` mass relations are derived
algebraically from the same vacuum scale.
-/

namespace PhysicsModel.ElectroweakBreaking

/-- A real pair representing the neutral gauge basis `(W³,B)`. -/
structure NeutralPair where
  weak : ℝ
  hypercharge : ℝ

namespace NeutralPair

instance : Add NeutralPair := ⟨fun x y => ⟨x.weak + y.weak, x.hypercharge + y.hypercharge⟩⟩
instance : SMul ℝ NeutralPair := ⟨fun a x => ⟨a * x.weak, a * x.hypercharge⟩⟩

@[ext] theorem ext {x y : NeutralPair}
    (weak : x.weak = y.weak) (hypercharge : x.hypercharge = y.hypercharge) : x = y := by
  cases x
  cases y
  simp_all

end NeutralPair

/-- Neutral gauge-boson mass operator induced by a Higgs VEV `v`. -/
noncomputable def neutralMassOperator (g gPrime vacuumScale : ℝ) (field : NeutralPair) : NeutralPair :=
  ⟨(vacuumScale ^ 2 / 4) * (g ^ 2 * field.weak - g * gPrime * field.hypercharge),
   (vacuumScale ^ 2 / 4) * (-g * gPrime * field.weak + gPrime ^ 2 * field.hypercharge)⟩

/-- The unnormalized electromagnetic direction in the `(W³,B)` basis. -/
def photonDirection (g gPrime : ℝ) : NeutralPair := ⟨gPrime, g⟩

/-- The orthogonal massive neutral direction. -/
def zDirection (g gPrime : ℝ) : NeutralPair := ⟨g, -gPrime⟩

/-- The photon direction is exactly the kernel of the Higgs mass operator. -/
theorem photon_massless (g gPrime vacuumScale : ℝ) :
    neutralMassOperator g gPrime vacuumScale (photonDirection g gPrime) = ⟨0, 0⟩ := by
  apply NeutralPair.ext <;> dsimp [neutralMassOperator, photonDirection] <;> ring

/-- The orthogonal `Z` direction is an eigenvector of the neutral mass matrix. -/
theorem z_mass_eigenvector (g gPrime vacuumScale : ℝ) :
    neutralMassOperator g gPrime vacuumScale (zDirection g gPrime) =
      ((vacuumScale ^ 2 / 4) * (g ^ 2 + gPrime ^ 2)) • zDirection g gPrime := by
  apply NeutralPair.ext
  · change _ = ((vacuumScale ^ 2 / 4) * (g ^ 2 + gPrime ^ 2)) * g
    dsimp [neutralMassOperator, zDirection]
    ring
  · change _ = ((vacuumScale ^ 2 / 4) * (g ^ 2 + gPrime ^ 2)) * (-gPrime)
    dsimp [neutralMassOperator, zDirection]
    ring

noncomputable def wMassSq (g vacuumScale : ℝ) : ℝ := g ^ 2 * vacuumScale ^ 2 / 4

noncomputable def zMassSq (g gPrime vacuumScale : ℝ) : ℝ :=
  (g ^ 2 + gPrime ^ 2) * vacuumScale ^ 2 / 4

theorem wMassSq_nonnegative (g vacuumScale : ℝ) : 0 ≤ wMassSq g vacuumScale := by
  unfold wMassSq
  positivity

theorem zMassSq_nonnegative (g gPrime vacuumScale : ℝ) :
    0 ≤ zMassSq g gPrime vacuumScale := by
  unfold zMassSq
  positivity

/-- Tree-level mass relation `m_W² = cos²θ_W m_Z²`. -/
theorem w_z_mass_relation {g gPrime vacuumScale : ℝ}
    (couplings_nonzero : g ^ 2 + gPrime ^ 2 ≠ 0) :
    wMassSq g vacuumScale =
      (g ^ 2 / (g ^ 2 + gPrime ^ 2)) * zMassSq g gPrime vacuumScale := by
  unfold wMassSq zMassSq
  field_simp

/-- The Higgs lower component is fixed by the unbroken generator `Q=T₃+Y`. -/
def electromagneticGenerator (weakIsospin hypercharge : ℚ) : ℚ :=
  weakIsospin + hypercharge

theorem higgs_vacuum_unbroken :
    electromagneticGenerator (-1 / 2) PhysicsModel.Electroweak.higgs.hypercharge = 0 := by
  norm_num [electromagneticGenerator, PhysicsModel.Electroweak.higgs]

/-- The upper Higgs component is charged under the same surviving generator. -/
theorem upper_higgs_charge :
    electromagneticGenerator (1 / 2) PhysicsModel.Electroweak.higgs.hypercharge = 1 := by
  norm_num [electromagneticGenerator, PhysicsModel.Electroweak.higgs]

/-- Electromagnetic coupling selected by the massless neutral direction. -/
noncomputable def electricCoupling (g gPrime : ℝ) : ℝ :=
  g * gPrime / Real.sqrt (g ^ 2 + gPrime ^ 2)

/-- Coupling to the photon direction is universally `e (T₃+Y)`. -/
theorem photon_coupling_is_electric {g gPrime weakIsospin hypercharge : ℝ}
    (positiveNorm : 0 < g ^ 2 + gPrime ^ 2) :
    g * (gPrime / Real.sqrt (g ^ 2 + gPrime ^ 2)) * weakIsospin +
        gPrime * (g / Real.sqrt (g ^ 2 + gPrime ^ 2)) * hypercharge =
      electricCoupling g gPrime * (weakIsospin + hypercharge) := by
  have hsqrt : Real.sqrt (g ^ 2 + gPrime ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 positiveNorm)
  unfold electricCoupling
  field_simp

end PhysicsModel.ElectroweakBreaking
