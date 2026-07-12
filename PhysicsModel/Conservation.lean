import PhysicsModel.Geometry4

/-! # Einstein equation implies stress-energy conservation

The covariant divergence is represented by a linear operator on rank-two
tensors.  Once the contracted Bianchi identity and metric compatibility make
the geometric side divergence-free, the checked Einstein equation forces the
matter stress tensor to be divergence-free for nonzero coupling.
-/

namespace PhysicsModel.Conservation

abbrev Vector4 := Fin 4 → ℝ
abbrev Divergence := EinsteinTensor4.Tensor →ₗ[ℝ] Vector4

theorem stressEnergy_conserved
    (sector : EinsteinSector EinsteinTensor4.Tensor)
    (divergence : Divergence)
    (equation : sector.lhs = sector.rhs)
    (einstein_bianchi : divergence sector.einstein = 0)
    (metric_compatible : divergence sector.metric = 0)
    (coupling_nonzero : sector.coupling ≠ 0) :
    divergence sector.stressEnergy = 0 := by
  have h := congrArg divergence equation
  simp only [EinsteinSector.lhs, EinsteinSector.rhs, map_add, map_smul,
    einstein_bianchi, metric_compatible, smul_zero, add_zero] at h
  have hzero : sector.coupling • divergence sector.stressEnergy = 0 := h.symm
  exact (smul_eq_zero.mp hzero).resolve_left coupling_nonzero

theorem stressEnergy_component_conserved
    (sector : EinsteinSector EinsteinTensor4.Tensor)
    (divergence : Divergence)
    (equation : sector.lhs = sector.rhs)
    (einstein_bianchi : divergence sector.einstein = 0)
    (metric_compatible : divergence sector.metric = 0)
    (coupling_nonzero : sector.coupling ≠ 0) (ν : Fin 4) :
    divergence sector.stressEnergy ν = 0 := by
  rw [stressEnergy_conserved sector divergence equation einstein_bianchi
    metric_compatible coupling_nonzero]
  rfl

/-- Flat vacuum realizes the conservation hypotheses for every linear divergence. -/
theorem flat_vacuum_conserved (metric inverseMetric : Geometry4.Metric)
    (coupling : ℝ) (coupling_nonzero : coupling ≠ 0)
    (divergence : Divergence) (metric_compatible : divergence metric = 0) :
    divergence
      (Geometry4.sector metric inverseMetric 0 0 0 0 coupling).stressEnergy = 0 := by
  apply stressEnergy_conserved
    (Geometry4.sector metric inverseMetric 0 0 0 0 coupling) divergence
  · exact EinsteinSector.einstein_from_zero_residual _
      (Geometry4.flat_vacuum_residual metric inverseMetric coupling)
  · simp only [Geometry4.sector]
    rw [Geometry4.riemann_zero, Geometry4.einsteinTensor_zero_curvature]
    exact map_zero divergence
  · exact metric_compatible
  · exact coupling_nonzero

end PhysicsModel.Conservation
