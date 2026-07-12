import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Wilson-to-Maxwell continuum limit

This proof is kept independent of the larger incidence-theory import graph.  A
square relational plaquette of spacing `h` and constant curvature `F` has angle
`h²F`; its Wilson density divided by area squared converges to `F²/2`.
-/

namespace PhysicsModel

open Filter Real Set
open scoped Topology

namespace ContinuumLimit

noncomputable def scaledWilsonDensity (field spacing : ℝ) : ℝ :=
  (1 - Real.cos (spacing ^ 2 * field)) / spacing ^ 4

theorem one_sub_cos_eq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul,
    ← Real.sin_sq_add_cos_sq (x / 2)]
  ring

theorem tendsto_sin_div_self :
    Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  simpa [div_eq_inv_mul, mul_comm] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

theorem square_field_tendsto_punctured (field : ℝ) (nonzero : field ≠ 0) :
    Tendsto (fun h : ℝ => h ^ 2 * field / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
      (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).mono_left inf_le_left
    simpa using ((hid.pow 2).mul tendsto_const_nhds).div_const 2
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [mem_compl_iff, mem_singleton_iff] at hh ⊢
    exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hh) nonzero) (by norm_num)

theorem scaledWilsonDensity_tendsto (field : ℝ) :
    Tendsto (scaledWilsonDensity field) (𝓝[≠] 0) (𝓝 (field ^ 2 / 2)) := by
  by_cases hfield : field = 0
  · subst field
    change Tendsto
      (fun spacing : ℝ => (1 - Real.cos (spacing ^ 2 * 0)) / spacing ^ 4)
      (𝓝[≠] 0) (𝓝 (0 ^ 2 / 2))
    simp
  · have hratio : Tendsto
        (fun h : ℝ => Real.sin (h ^ 2 * field / 2) / (h ^ 2 * field / 2))
        (𝓝[≠] 0) (𝓝 1) :=
      tendsto_sin_div_self.comp (square_field_tendsto_punctured field hfield)
    have htarget : Tendsto
        (fun h : ℝ => (field ^ 2 / 2) *
          (Real.sin (h ^ 2 * field / 2) / (h ^ 2 * field / 2)) ^ 2)
        (𝓝[≠] 0) (𝓝 (field ^ 2 / 2)) := by
      convert tendsto_const_nhds.mul (hratio.pow 2) using 1
      all_goals norm_num
    apply htarget.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [mem_compl_iff, mem_singleton_iff] at hh
    unfold scaledWilsonDensity
    rw [one_sub_cos_eq]
    field_simp

theorem dyadic_spacing_tendsto_punctured :
    Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝[≠] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · exact Eventually.of_forall fun n => by
      simp [mem_compl_iff, mem_singleton_iff]

theorem dyadic_scaledWilsonDensity_tendsto (field : ℝ) :
    Tendsto (fun n : ℕ => scaledWilsonDensity field ((2 : ℝ)⁻¹ ^ n))
      atTop (𝓝 (field ^ 2 / 2)) :=
  (scaledWilsonDensity_tendsto field).comp dyadic_spacing_tendsto_punctured

end ContinuumLimit
end PhysicsModel
