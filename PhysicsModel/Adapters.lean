import PhysicsModel.Synthesis
import IncRQM.Measurement.Relative
import IncRQM.Cell.Complex
import RelationalTime.Inc.Adapter

/-! # Certified reuse of Inc, relational-time, and Inc--RQM -/

namespace PhysicsModel

open IncRQM

universe u v w

/-- Existing Inc--RQM relative observations directly realize relational facts. -/
theorem relative_record_frame_independent
    {V System : Type u} {G Observer : Type v} {Outcome : Type w}
    [AbelianGaugeGroup G]
    (system : System) (observer : Observer)
    (experiment : InterferenceExperiment V G Outcome)
    (frame : V → G) (field : LinkField V G) :
    recordRelative (V := V) (G := G) system observer experiment
        (gaugeTransform frame field) =
      recordRelative (V := V) (G := G) system observer experiment field :=
  recordRelative_gauge_invariant system observer experiment frame field

/-- Existing Inc gluing supplies a concrete case where an internal relation disappears
under coarse composition while exterior relations survive. -/
theorem inc_internal_relation_cancels :
    TwoSquareComplex.complex.gluedCoefficient
      TwoSquareComplex.Cell.left TwoSquareComplex.Cell.right
      TwoSquareComplex.Edge.shared = 0 :=
  TwoSquareComplex.shared_cancels

end PhysicsModel
