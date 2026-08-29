import Huarongdao.CaoGuanGeometry
import Huarongdao.DiscreteGeometry
import Huarongdao.ClassicFullSpace
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic

namespace Huarongdao
namespace CaoFiberMetrics

open CaoGuanGeometry
open ClassicFullSpace
open ClassicStateSpaceKernel
open DiscreteGeometry

/-!
# Metric layer for Cao Cao fibres

The definitions in `CaoGuanGeometry` are semantic definitions over all legal
labelled states.  This file adds the metric facts that are independent of a
particular finite enumeration.  In particular:

* graph distance is an extended metric and may be `∞`;
* the minimum distance between two fibres is a set separation quantity and
  does not, in general, satisfy a triangle inequality;
* Hausdorff edistance is the metric quantity for which the triangle
  inequality is available.

The executable 12 by 12 tables are produced by `CaoFiberMetricsMain.lean`
on the finite equal-shape component containing the classical initial layout.
-/

open scoped BigOperators ENNReal

abbrev CaoFiber := CaoGuanGeometry.caoFiber

noncomputable def caoPositionHausdorffEDist
    (left right : CaoPosition) : ℝ≥0∞ :=
  graphHausdorffEDist concreteStateGraph
    (caoFiber left) (caoFiber right)

theorem caoPositionGraphEdist_self (position : CaoPosition) :
    caoPositionGraphEdist position position = 0 := by
  simp [caoPositionGraphEdist]

theorem caoPositionGraphEdist_comm
    (left right : CaoPosition) :
    caoPositionGraphEdist left right =
      caoPositionGraphEdist right left := by
  simp [caoPositionGraphEdist, SimpleGraph.edist_comm]

theorem caoPositionGraphEdist_triangle
    (left middle right : CaoPosition) :
    caoPositionGraphEdist left right ≤
      caoPositionGraphEdist left middle +
        caoPositionGraphEdist middle right := by
  exact SimpleGraph.edist_triangle

theorem concreteStateGraphEdist_self (state : ValidClassicState) :
    concreteStateGraphEdist state state = 0 := by
  simp [concreteStateGraphEdist]

theorem concreteStateGraphEdist_comm
    (source target : ValidClassicState) :
    concreteStateGraphEdist source target =
      concreteStateGraphEdist target source := by
  simp [concreteStateGraphEdist, SimpleGraph.edist_comm]

theorem concreteStateGraphEdist_triangle
    (source middle target : ValidClassicState) :
    concreteStateGraphEdist source target ≤
      concreteStateGraphEdist source middle +
        concreteStateGraphEdist middle target := by
  exact SimpleGraph.edist_triangle

theorem caoFiberMinEdist_comm
    (left right : CaoPosition) :
    caoFiberMinEdist left right =
      caoFiberMinEdist right left := by
  unfold caoFiberMinEdist
  apply le_antisymm
  · refine le_iInf fun source => ?_
    refine le_iInf fun target => ?_
    calc
      (⨅ source : {state : ValidClassicState // state ∈ caoFiber left},
        ⨅ target : {state : ValidClassicState // state ∈ caoFiber right},
          concreteStateGraphEdist source.1 target.1) ≤
        concreteStateGraphEdist target.1 source.1 :=
          iInf_le_of_le target (iInf_le_of_le source le_rfl)
      _ = concreteStateGraphEdist source.1 target.1 :=
        concreteStateGraphEdist_comm _ _
  · refine le_iInf fun target => ?_
    refine le_iInf fun source => ?_
    calc
      (⨅ target : {state : ValidClassicState // state ∈ caoFiber right},
        ⨅ source : {state : ValidClassicState // state ∈ caoFiber left},
          concreteStateGraphEdist target.1 source.1) ≤
        concreteStateGraphEdist source.1 target.1 :=
          iInf_le_of_le source (iInf_le_of_le target le_rfl)
      _ = concreteStateGraphEdist target.1 source.1 :=
        concreteStateGraphEdist_comm _ _

theorem caoPositionHausdorffEDist_comm
    (left right : CaoPosition) :
    caoPositionHausdorffEDist left right =
      caoPositionHausdorffEDist right left := by
  exact graphHausdorffEDist_comm _ _ _

theorem caoPositionHausdorffEDist_triangle
    (left middle right : CaoPosition) :
    caoPositionHausdorffEDist left right ≤
      caoPositionHausdorffEDist left middle +
        caoPositionHausdorffEDist middle right := by
  exact graphHausdorffEDist_triangle _ _ _ _

end CaoFiberMetrics
end Huarongdao
