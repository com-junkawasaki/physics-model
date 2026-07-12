import PhysicsModel.Minkowski4
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Arbitrary Lorentz transformations in 3+1 dimensions

A Lorentz transformation is represented intrinsically as an invertible real
linear map preserving the Minkowski bilinear form.  This is the coordinate-free
content of the matrix equation `Λᵀ η Λ = η`.
-/

namespace PhysicsModel.GeneralLorentz4

abbrev SpacetimeVector := Fin 4 → ℝ

/-- Minkowski bilinear form with signature `(+---)`. -/
def minkowskiInner (p q : SpacetimeVector) : ℝ :=
  p 0 * q 0 - p 1 * q 1 - p 2 * q 2 - p 3 * q 3

def normSq (p : SpacetimeVector) : ℝ := minkowskiInner p p

theorem minkowskiInner_symmetric (p q : SpacetimeVector) :
    minkowskiInner p q = minkowskiInner q p := by
  unfold minkowskiInner
  ring

theorem minkowskiInner_add_left (p q r : SpacetimeVector) :
    minkowskiInner (p + q) r = minkowskiInner p r + minkowskiInner q r := by
  unfold minkowskiInner
  simp only [Pi.add_apply]
  ring

theorem minkowskiInner_smul_left (a : ℝ) (p q : SpacetimeVector) :
    minkowskiInner (a • p) q = a * minkowskiInner p q := by
  unfold minkowskiInner
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- An arbitrary invertible linear transformation satisfying `Λᵀ η Λ = η`. -/
structure Transform where
  toLinearEquiv : SpacetimeVector ≃ₗ[ℝ] SpacetimeVector
  preserves_inner : ∀ p q,
    minkowskiInner (toLinearEquiv p) (toLinearEquiv q) = minkowskiInner p q

namespace Transform

@[ext] theorem ext {first second : Transform}
    (h : first.toLinearEquiv = second.toLinearEquiv) : first = second := by
  cases first
  cases second
  cases h
  rfl

instance : CoeFun Transform (fun _ => SpacetimeVector → SpacetimeVector) :=
  ⟨fun lorentz => lorentz.toLinearEquiv⟩

/-- The identity frame transformation is Lorentz. -/
def identity : Transform where
  toLinearEquiv := LinearEquiv.refl ℝ SpacetimeVector
  preserves_inner := by intros; rfl

@[simp] theorem identity_apply (p : SpacetimeVector) : identity p = p := rfl

/-- Lorentz transformations are closed under composition. -/
def comp (second first : Transform) : Transform where
  toLinearEquiv := first.toLinearEquiv.trans second.toLinearEquiv
  preserves_inner := by
    intro p q
    change minkowskiInner (second.toLinearEquiv (first.toLinearEquiv p))
      (second.toLinearEquiv (first.toLinearEquiv q)) = minkowskiInner p q
    rw [second.preserves_inner, first.preserves_inner]

@[simp] theorem comp_apply (second first : Transform) (p : SpacetimeVector) :
    comp second first p = second (first p) := rfl

@[simp] theorem identity_comp (lorentz : Transform) :
    comp identity lorentz = lorentz := by
  apply Transform.ext
  apply LinearEquiv.ext
  intro p
  rfl

@[simp] theorem comp_identity (lorentz : Transform) :
    comp lorentz identity = lorentz := by
  apply Transform.ext
  apply LinearEquiv.ext
  intro p
  rfl

theorem comp_assoc (third second first : Transform) :
    comp third (comp second first) = comp (comp third second) first := by
  apply Transform.ext
  apply LinearEquiv.ext
  intro p
  rfl

/-- The inverse of every Lorentz transformation is Lorentz. -/
def inverse (lorentz : Transform) : Transform where
  toLinearEquiv := lorentz.toLinearEquiv.symm
  preserves_inner := by
    intro p q
    have h := lorentz.preserves_inner
      (lorentz.toLinearEquiv.symm p) (lorentz.toLinearEquiv.symm q)
    simpa using h.symm

@[simp] theorem inverse_apply_apply (lorentz : Transform) (p : SpacetimeVector) :
    inverse lorentz (lorentz p) = p := by
  exact lorentz.toLinearEquiv.symm_apply_apply p

@[simp] theorem apply_inverse_apply (lorentz : Transform) (p : SpacetimeVector) :
    lorentz (inverse lorentz p) = p := by
  exact lorentz.toLinearEquiv.apply_symm_apply p

theorem inverse_comp (lorentz : Transform) :
    comp (inverse lorentz) lorentz = identity := by
  cases lorentz with
  | mk equivalence preservation =>
      apply Transform.ext
      apply LinearEquiv.ext
      intro p
      simp [comp, inverse, identity]

theorem comp_inverse (lorentz : Transform) :
    comp lorentz (inverse lorentz) = identity := by
  cases lorentz with
  | mk equivalence preservation =>
      apply Transform.ext
      apply LinearEquiv.ext
      intro p
      simp [comp, inverse, identity]

/-- Every certified Lorentz transformation preserves the Minkowski norm. -/
theorem normSq_invariant (lorentz : Transform) (p : SpacetimeVector) :
    normSq (lorentz p) = normSq p :=
  lorentz.preserves_inner p p

theorem mass_shell_preserved (lorentz : Transform) (p : SpacetimeVector) (mass : ℝ)
    (onShell : normSq p = mass ^ 2) :
    normSq (lorentz p) = mass ^ 2 := by
  rw [normSq_invariant, onShell]

end Transform

/-- Coordinate embedding of the existing four-momentum representation. -/
def ofFourMomentum (p : Minkowski4.FourMomentum) : SpacetimeVector
  | 0 => p.energy
  | 1 => p.px
  | 2 => p.py
  | 3 => p.pz

theorem normSq_ofFourMomentum (p : Minkowski4.FourMomentum) :
    normSq (ofFourMomentum p) = Minkowski4.minkowskiNormSq p := by
  unfold normSq minkowskiInner ofFourMomentum Minkowski4.minkowskiNormSq
  ring

/-- The previously checked physical mass shell is invariant under every Lorentz transformation. -/
theorem fourMomentum_mass_shell_preserved (lorentz : Transform)
    (p : Minkowski4.FourMomentum) (mass : ℝ)
    (onShell : Minkowski4.minkowskiNormSq p = mass ^ 2) :
    normSq (lorentz (ofFourMomentum p)) = mass ^ 2 := by
  rw [Transform.normSq_invariant, normSq_ofFourMomentum, onShell]

end PhysicsModel.GeneralLorentz4
