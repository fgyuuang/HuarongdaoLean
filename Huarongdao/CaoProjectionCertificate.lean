import Huarongdao.CaoProjection
import Std.Tactic

namespace Huarongdao
namespace ClassicStateSpaceKernel

/- Concrete legal representatives for 17 observed neighbor pairs of the
   twelve Cao Cao position classes. State ids refer to frontend/graph.json.

   This file certifies one concrete one-step witness for each listed pair.
   It does not, by itself, prove that these are all edges of the quotient
   relation CaoClassAdjacent. -/
def classicCaoWitnessState16 : ValidClassicState :=
  ⟨{ positions := #[⟨1,0⟩, ⟨1,3⟩, ⟨0,0⟩, ⟨3,0⟩, ⟨0,2⟩, ⟨3,2⟩, ⟨1,4⟩, ⟨2,4⟩, ⟨0,4⟩, ⟨3,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState29 : ValidClassicState :=
  ⟨{ positions := #[⟨1,1⟩, ⟨1,3⟩, ⟨0,0⟩, ⟨3,0⟩, ⟨0,2⟩, ⟨3,2⟩, ⟨1,4⟩, ⟨2,4⟩, ⟨0,4⟩, ⟨3,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState81 : ValidClassicState :=
  ⟨{ positions := #[⟨1,0⟩, ⟨2,2⟩, ⟨0,2⟩, ⟨3,0⟩, ⟨1,2⟩, ⟨3,3⟩, ⟨1,4⟩, ⟨2,3⟩, ⟨0,4⟩, ⟨2,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState85 : ValidClassicState :=
  ⟨{ positions := #[⟨1,0⟩, ⟨0,2⟩, ⟨0,0⟩, ⟨3,2⟩, ⟨0,3⟩, ⟨2,2⟩, ⟨1,3⟩, ⟨2,4⟩, ⟨1,4⟩, ⟨3,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState101 : ValidClassicState :=
  ⟨{ positions := #[⟨0,0⟩, ⟨2,2⟩, ⟨0,2⟩, ⟨3,0⟩, ⟨1,2⟩, ⟨3,3⟩, ⟨1,4⟩, ⟨2,3⟩, ⟨0,4⟩, ⟨2,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState106 : ValidClassicState :=
  ⟨{ positions := #[⟨2,0⟩, ⟨0,2⟩, ⟨0,0⟩, ⟨3,2⟩, ⟨0,3⟩, ⟨2,2⟩, ⟨1,3⟩, ⟨2,4⟩, ⟨1,4⟩, ⟨3,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState932 : ValidClassicState :=
  ⟨{ positions := #[⟨2,0⟩, ⟨0,2⟩, ⟨1,0⟩, ⟨3,3⟩, ⟨0,0⟩, ⟨2,3⟩, ⟨0,3⟩, ⟨1,4⟩, ⟨0,4⟩, ⟨1,3⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState940 : ValidClassicState :=
  ⟨{ positions := #[⟨0,0⟩, ⟨2,2⟩, ⟨0,3⟩, ⟨2,0⟩, ⟨1,3⟩, ⟨3,0⟩, ⟨2,4⟩, ⟨3,3⟩, ⟨2,3⟩, ⟨3,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState990 : ValidClassicState :=
  ⟨{ positions := #[⟨2,1⟩, ⟨0,2⟩, ⟨1,0⟩, ⟨3,3⟩, ⟨0,0⟩, ⟨2,3⟩, ⟨0,3⟩, ⟨1,4⟩, ⟨0,4⟩, ⟨1,3⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState1004 : ValidClassicState :=
  ⟨{ positions := #[⟨0,1⟩, ⟨2,2⟩, ⟨0,3⟩, ⟨2,0⟩, ⟨1,3⟩, ⟨3,0⟩, ⟨2,4⟩, ⟨3,3⟩, ⟨2,3⟩, ⟨3,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState14499 : ValidClassicState :=
  ⟨{ positions := #[⟨1,1⟩, ⟨2,4⟩, ⟨1,3⟩, ⟨3,0⟩, ⟨0,3⟩, ⟨3,2⟩, ⟨2,3⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨2,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState14701 : ValidClassicState :=
  ⟨{ positions := #[⟨1,1⟩, ⟨0,4⟩, ⟨0,0⟩, ⟨2,3⟩, ⟨0,2⟩, ⟨3,3⟩, ⟨2,0⟩, ⟨1,3⟩, ⟨1,0⟩, ⟨3,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState14980 : ValidClassicState :=
  ⟨{ positions := #[⟨0,1⟩, ⟨2,4⟩, ⟨1,3⟩, ⟨3,0⟩, ⟨0,3⟩, ⟨3,2⟩, ⟨2,3⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨2,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState15160 : ValidClassicState :=
  ⟨{ positions := #[⟨2,1⟩, ⟨0,4⟩, ⟨0,0⟩, ⟨2,3⟩, ⟨0,2⟩, ⟨3,3⟩, ⟨2,0⟩, ⟨1,3⟩, ⟨1,0⟩, ⟨3,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState16275 : ValidClassicState :=
  ⟨{ positions := #[⟨1,1⟩, ⟨2,4⟩, ⟨0,3⟩, ⟨3,0⟩, ⟨0,1⟩, ⟨3,2⟩, ⟨1,4⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨2,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState16509 : ValidClassicState :=
  ⟨{ positions := #[⟨1,2⟩, ⟨2,4⟩, ⟨0,3⟩, ⟨3,0⟩, ⟨0,1⟩, ⟨3,2⟩, ⟨1,4⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨2,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17255 : ValidClassicState :=
  ⟨{ positions := #[⟨1,2⟩, ⟨2,4⟩, ⟨0,3⟩, ⟨2,0⟩, ⟨0,1⟩, ⟨3,0⟩, ⟨1,4⟩, ⟨1,1⟩, ⟨0,0⟩, ⟨1,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17278 : ValidClassicState :=
  ⟨{ positions := #[⟨1,2⟩, ⟨0,4⟩, ⟨1,0⟩, ⟨3,3⟩, ⟨0,0⟩, ⟨3,1⟩, ⟨2,1⟩, ⟨2,4⟩, ⟨2,0⟩, ⟨3,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17329 : ValidClassicState :=
  ⟨{ positions := #[⟨2,2⟩, ⟨2,4⟩, ⟨0,3⟩, ⟨2,0⟩, ⟨0,1⟩, ⟨3,0⟩, ⟨1,4⟩, ⟨1,1⟩, ⟨0,0⟩, ⟨1,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17346 : ValidClassicState :=
  ⟨{ positions := #[⟨0,2⟩, ⟨0,4⟩, ⟨1,0⟩, ⟨3,3⟩, ⟨0,0⟩, ⟨3,1⟩, ⟨2,1⟩, ⟨2,4⟩, ⟨2,0⟩, ⟨3,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17685 : ValidClassicState :=
  ⟨{ positions := #[⟨2,1⟩, ⟨2,4⟩, ⟨1,0⟩, ⟨1,2⟩, ⟨0,0⟩, ⟨0,2⟩, ⟨2,0⟩, ⟨0,4⟩, ⟨1,4⟩, ⟨3,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17693 : ValidClassicState :=
  ⟨{ positions := #[⟨0,1⟩, ⟨0,4⟩, ⟨2,2⟩, ⟨2,0⟩, ⟨3,2⟩, ⟨3,0⟩, ⟨3,4⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨2,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17771 : ValidClassicState :=
  ⟨{ positions := #[⟨2,2⟩, ⟨2,4⟩, ⟨1,0⟩, ⟨1,2⟩, ⟨0,0⟩, ⟨0,2⟩, ⟨2,0⟩, ⟨0,4⟩, ⟨1,4⟩, ⟨3,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17780 : ValidClassicState :=
  ⟨{ positions := #[⟨0,2⟩, ⟨0,4⟩, ⟨2,2⟩, ⟨2,0⟩, ⟨3,2⟩, ⟨3,0⟩, ⟨3,4⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨2,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17790 : ValidClassicState :=
  ⟨{ positions := #[⟨2,2⟩, ⟨0,4⟩, ⟨0,2⟩, ⟨2,0⟩, ⟨0,0⟩, ⟨3,0⟩, ⟨1,3⟩, ⟨1,2⟩, ⟨1,0⟩, ⟨1,1⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17851 : ValidClassicState :=
  ⟨{ positions := #[⟨0,2⟩, ⟨2,4⟩, ⟨1,0⟩, ⟨3,2⟩, ⟨0,0⟩, ⟨3,0⟩, ⟨2,2⟩, ⟨2,3⟩, ⟨2,1⟩, ⟨2,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17894 : ValidClassicState :=
  ⟨{ positions := #[⟨2,3⟩, ⟨0,4⟩, ⟨0,2⟩, ⟨2,0⟩, ⟨0,0⟩, ⟨3,0⟩, ⟨1,3⟩, ⟨1,2⟩, ⟨1,0⟩, ⟨1,1⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState17967 : ValidClassicState :=
  ⟨{ positions := #[⟨0,3⟩, ⟨2,4⟩, ⟨1,0⟩, ⟨3,2⟩, ⟨0,0⟩, ⟨3,0⟩, ⟨2,2⟩, ⟨2,3⟩, ⟨2,1⟩, ⟨2,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState23949 : ValidClassicState :=
  ⟨{ positions := #[⟨0,3⟩, ⟨2,2⟩, ⟨3,0⟩, ⟨2,0⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨0,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨1,2⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState23962 : ValidClassicState :=
  ⟨{ positions := #[⟨2,3⟩, ⟨0,2⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨3,0⟩, ⟨2,0⟩, ⟨0,3⟩, ⟨3,2⟩, ⟨2,2⟩, ⟨0,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState24026 : ValidClassicState :=
  ⟨{ positions := #[⟨1,3⟩, ⟨2,2⟩, ⟨3,0⟩, ⟨2,0⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨0,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨1,2⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState24037 : ValidClassicState :=
  ⟨{ positions := #[⟨1,3⟩, ⟨0,2⟩, ⟨1,0⟩, ⟨0,0⟩, ⟨3,0⟩, ⟨2,0⟩, ⟨0,3⟩, ⟨3,2⟩, ⟨2,2⟩, ⟨0,4⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState25062 : ValidClassicState :=
  ⟨{ positions := #[⟨1,3⟩, ⟨0,1⟩, ⟨0,3⟩, ⟨3,2⟩, ⟨2,0⟩, ⟨3,0⟩, ⟨0,2⟩, ⟨3,4⟩, ⟨1,0⟩, ⟨0,0⟩] }, by
    unfold ValidState
    native_decide⟩

def classicCaoWitnessState25080 : ValidClassicState :=
  ⟨{ positions := #[⟨1,2⟩, ⟨0,1⟩, ⟨0,3⟩, ⟨3,2⟩, ⟨2,0⟩, ⟨3,0⟩, ⟨0,2⟩, ⟨3,4⟩, ⟨1,0⟩, ⟨0,0⟩] }, by
    unfold ValidState
    native_decide⟩


theorem classicCaoClassDistance_00_01 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState940)
      (caoPositionObservation.classOf classicCaoWitnessState1004) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .down⟩)
      (by
        change tryMove (classicCaoWitnessState940.1) .caoCao .down =
          some classicCaoWitnessState1004.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_00_10 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState81)
      (caoPositionObservation.classOf classicCaoWitnessState101) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .left⟩)
      (by
        change tryMove (classicCaoWitnessState81.1) .caoCao .left =
          some classicCaoWitnessState101.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_01_02 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState17693)
      (caoPositionObservation.classOf classicCaoWitnessState17780) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .down⟩)
      (by
        change tryMove (classicCaoWitnessState17693.1) .caoCao .down =
          some classicCaoWitnessState17780.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_01_11 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState14499)
      (caoPositionObservation.classOf classicCaoWitnessState14980) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .left⟩)
      (by
        change tryMove (classicCaoWitnessState14499.1) .caoCao .left =
          some classicCaoWitnessState14980.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_02_03 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState17851)
      (caoPositionObservation.classOf classicCaoWitnessState17967) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .down⟩)
      (by
        change tryMove (classicCaoWitnessState17851.1) .caoCao .down =
          some classicCaoWitnessState17967.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_02_12 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState17278)
      (caoPositionObservation.classOf classicCaoWitnessState17346) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .left⟩)
      (by
        change tryMove (classicCaoWitnessState17278.1) .caoCao .left =
          some classicCaoWitnessState17346.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_03_13 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState23949)
      (caoPositionObservation.classOf classicCaoWitnessState24026) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .right⟩)
      (by
        change tryMove (classicCaoWitnessState23949.1) .caoCao .right =
          some classicCaoWitnessState24026.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_10_11 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState16)
      (caoPositionObservation.classOf classicCaoWitnessState29) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .down⟩)
      (by
        change tryMove (classicCaoWitnessState16.1) .caoCao .down =
          some classicCaoWitnessState29.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_10_20 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState85)
      (caoPositionObservation.classOf classicCaoWitnessState106) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .right⟩)
      (by
        change tryMove (classicCaoWitnessState85.1) .caoCao .right =
          some classicCaoWitnessState106.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_11_12 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState16275)
      (caoPositionObservation.classOf classicCaoWitnessState16509) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .down⟩)
      (by
        change tryMove (classicCaoWitnessState16275.1) .caoCao .down =
          some classicCaoWitnessState16509.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_11_21 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState14701)
      (caoPositionObservation.classOf classicCaoWitnessState15160) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .right⟩)
      (by
        change tryMove (classicCaoWitnessState14701.1) .caoCao .right =
          some classicCaoWitnessState15160.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_12_13 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState25062)
      (caoPositionObservation.classOf classicCaoWitnessState25080) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .up⟩)
      (by
        change tryMove (classicCaoWitnessState25062.1) .caoCao .up =
          some classicCaoWitnessState25080.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_12_22 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState17255)
      (caoPositionObservation.classOf classicCaoWitnessState17329) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .right⟩)
      (by
        change tryMove (classicCaoWitnessState17255.1) .caoCao .right =
          some classicCaoWitnessState17329.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_13_23 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState23962)
      (caoPositionObservation.classOf classicCaoWitnessState24037) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .left⟩)
      (by
        change tryMove (classicCaoWitnessState23962.1) .caoCao .left =
          some classicCaoWitnessState24037.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_20_21 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState932)
      (caoPositionObservation.classOf classicCaoWitnessState990) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .down⟩)
      (by
        change tryMove (classicCaoWitnessState932.1) .caoCao .down =
          some classicCaoWitnessState990.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_21_22 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState17685)
      (caoPositionObservation.classOf classicCaoWitnessState17771) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .down⟩)
      (by
        change tryMove (classicCaoWitnessState17685.1) .caoCao .down =
          some classicCaoWitnessState17771.1
        native_decide)
      (by native_decide))


theorem classicCaoClassDistance_22_23 :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState17790)
      (caoPositionObservation.classOf classicCaoWitnessState17894) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, .down⟩)
      (by
        change tryMove (classicCaoWitnessState17790.1) .caoCao .down =
          some classicCaoWitnessState17894.1
        native_decide)
      (by native_decide))

/-- One concrete one-step witness for each of the 17 listed Cao Cao class pairs.

This is an existence certificate for the listed pairs, not an edge-completeness
certificate for CaoClassAdjacent. In particular, no field states that every
adjacent pair of quotient nodes occurs among these 17 fields. -/
structure CaoClassWitnessCertificate where
  pair_00_01 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState940)
    (caoPositionObservation.classOf classicCaoWitnessState1004)
  pair_00_10 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState81)
    (caoPositionObservation.classOf classicCaoWitnessState101)
  pair_01_02 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState17693)
    (caoPositionObservation.classOf classicCaoWitnessState17780)
  pair_01_11 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState14499)
    (caoPositionObservation.classOf classicCaoWitnessState14980)
  pair_02_03 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState17851)
    (caoPositionObservation.classOf classicCaoWitnessState17967)
  pair_02_12 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState17278)
    (caoPositionObservation.classOf classicCaoWitnessState17346)
  pair_03_13 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState23949)
    (caoPositionObservation.classOf classicCaoWitnessState24026)
  pair_10_11 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState16)
    (caoPositionObservation.classOf classicCaoWitnessState29)
  pair_10_20 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState85)
    (caoPositionObservation.classOf classicCaoWitnessState106)
  pair_11_12 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState16275)
    (caoPositionObservation.classOf classicCaoWitnessState16509)
  pair_11_21 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState14701)
    (caoPositionObservation.classOf classicCaoWitnessState15160)
  pair_12_13 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState25062)
    (caoPositionObservation.classOf classicCaoWitnessState25080)
  pair_12_22 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState17255)
    (caoPositionObservation.classOf classicCaoWitnessState17329)
  pair_13_23 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState23962)
    (caoPositionObservation.classOf classicCaoWitnessState24037)
  pair_20_21 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState932)
    (caoPositionObservation.classOf classicCaoWitnessState990)
  pair_21_22 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState17685)
    (caoPositionObservation.classOf classicCaoWitnessState17771)
  pair_22_23 : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState17790)
    (caoPositionObservation.classOf classicCaoWitnessState17894)

/-- The bundled witnesses for the 17 listed pairs in the twelve-point
projection. -/
theorem classicCaoClassWitnesses : CaoClassWitnessCertificate :=
  {
  pair_00_01 := classicCaoClassDistance_00_01
  pair_00_10 := classicCaoClassDistance_00_10
  pair_01_02 := classicCaoClassDistance_01_02
  pair_01_11 := classicCaoClassDistance_01_11
  pair_02_03 := classicCaoClassDistance_02_03
  pair_02_12 := classicCaoClassDistance_02_12
  pair_03_13 := classicCaoClassDistance_03_13
  pair_10_11 := classicCaoClassDistance_10_11
  pair_10_20 := classicCaoClassDistance_10_20
  pair_11_12 := classicCaoClassDistance_11_12
  pair_11_21 := classicCaoClassDistance_11_21
  pair_12_13 := classicCaoClassDistance_12_13
  pair_12_22 := classicCaoClassDistance_12_22
  pair_13_23 := classicCaoClassDistance_13_23
  pair_20_21 := classicCaoClassDistance_20_21
  pair_21_22 := classicCaoClassDistance_21_22
  pair_22_23 := classicCaoClassDistance_22_23
  }

end ClassicStateSpaceKernel
end Huarongdao
