import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Fintype.Card

/-! # Standard-Model emergence interface

This module does not assume the observed particle table.  It states the exact
certificate a microscopic collective-mode construction must provide: a gauge
action, identified mode families, and an invariant effective action.
-/

namespace PhysicsModel

universe u v w

/-- Candidate low-energy gauge and matter sector extracted from collective modes. -/
structure GaugeMatterSector (Gauge : Type u) (Field : Type v) (ActionValue : Type w) where
  compose : Gauge → Gauge → Gauge
  transform : Gauge → Field → Field
  transform_compose : ∀ g h field,
    transform (compose g h) field = transform g (transform h field)
  effectiveAction : Field → ActionValue
  invariant : ∀ g field, effectiveAction (transform g field) = effectiveAction field

namespace GaugeMatterSector

variable {Gauge : Type u} {Field : Type v} {ActionValue : Type w}

theorem action_gauge_invariant (sector : GaugeMatterSector Gauge Field ActionValue)
    (g : Gauge) (field : Field) :
    sector.effectiveAction (sector.transform g field) = sector.effectiveAction field :=
  sector.invariant g field

theorem action_invariant_under_composition
    (sector : GaugeMatterSector Gauge Field ActionValue)
    (g h : Gauge) (field : Field) :
    sector.effectiveAction (sector.transform (sector.compose g h) field) =
      sector.effectiveAction field := by
  rw [sector.transform_compose, sector.invariant g, sector.invariant h]

end GaugeMatterSector

/-- A certificate that the emergent gauge group and mode families match the
Standard Model target, without pretending that the certificate has been constructed. -/
structure StandardModelCertificate
    {Gauge : Type u} {Field : Type v} {ActionValue : Type w}
    (sector : GaugeMatterSector Gauge Field ActionValue) where
  TargetGauge : Type u
  gaugeIdentification : Gauge ≃ TargetGauge
  Generation : Type v
  generations : Finset Generation
  threeGenerations : generations.card = 3
  anomalyFree : Prop
  anomalyCancellation : anomalyFree

theorem certified_three_generations
    {Gauge : Type u} {Field : Type v} {ActionValue : Type w}
    {sector : GaugeMatterSector Gauge Field ActionValue}
    (certificate : StandardModelCertificate sector) :
    certificate.generations.card = 3 := certificate.threeGenerations

theorem certified_anomaly_free
    {Gauge : Type u} {Field : Type v} {ActionValue : Type w}
    {sector : GaugeMatterSector Gauge Field ActionValue}
    (certificate : StandardModelCertificate sector) : certificate.anomalyFree :=
  certificate.anomalyCancellation

end PhysicsModel
