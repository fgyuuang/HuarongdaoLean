import Huarongdao.ClassicComponentSymmetry

open Huarongdao
open Huarongdao.ClassicFullSpace

def positionJson (position : Pos) : String :=
  "[" ++ toString position.x ++ "," ++ toString position.y ++ "]"

def componentMapGet (componentMap : Array Nat) (id count : Nat) : Nat :=
  componentMap.getD id count

def rotationComponent
    (horizontalMap verticalMap : Array Nat) (id count : Nat) : Nat :=
  componentMapGet horizontalMap
    (componentMapGet verticalMap id count) count

def kleinOrbitRepresentative
    (horizontalMap verticalMap : Array Nat) (id count : Nat) : Nat :=
  let horizontal := componentMapGet horizontalMap id count
  let vertical := componentMapGet verticalMap id count
  let rotation := rotationComponent horizontalMap verticalMap id count
  min (min id horizontal) (min vertical rotation)

def kleinComponentOrbitCount
    (horizontalMap verticalMap : Array Nat) : Nat := Id.run do
  let count := min horizontalMap.size verticalMap.size
  let mut orbitRepresentatives : Std.HashSet Nat := {}
  for id in List.range count do
    orbitRepresentatives := orbitRepresentatives.insert
      (kleinOrbitRepresentative horizontalMap verticalMap id count)
  return orbitRepresentatives.size

def representativeJson
    (horizontalMap verticalMap : Array Nat)
    (componentCount id : Nat) (summary : ComponentSummary) : String :=
  let positions :=
    String.intercalate "," <|
      Piece.all.map fun piece =>
        positionJson (summary.representative.pos piece)
  let horizontal :=
    componentMapGet horizontalMap id componentCount
  let vertical :=
    componentMapGet verticalMap id componentCount
  let rotation :=
    rotationComponent horizontalMap verticalMap id componentCount
  let orbit :=
    kleinOrbitRepresentative horizontalMap verticalMap id componentCount
  "{\"id\":" ++ toString id ++
    ",\"key\":\"" ++ summary.representative.key ++
    "\",\"positions\":[" ++ positions ++
    "],\"stateCount\":" ++ toString summary.stateCount ++
    ",\"directedEdgeCount\":" ++ toString summary.directedEdgeCount ++
    ",\"containsClassic\":" ++ toString summary.containsClassic ++
    ",\"horizontalComponent\":" ++ toString horizontal ++
    ",\"verticalComponent\":" ++ toString vertical ++
    ",\"rotationComponent\":" ++ toString rotation ++
    ",\"kleinOrbit\":" ++ toString orbit ++
    ",\"horizontalFixed\":" ++ toString (horizontal == id) ++
    ",\"verticalFixed\":" ++ toString (vertical == id) ++
    ",\"rotationFixed\":" ++ toString (rotation == id) ++ "}"

def statePositionsJson (state : State) : String :=
  let positions :=
    String.intercalate "," <|
      Piece.all.map fun piece =>
        positionJson (state.pos piece)
  "[" ++ positions ++ "]"

def fullSpaceJson : String :=
  let result := analyze
  let symmetry := analyzeComponentSymmetries
  let componentCount := result.summaries.size
  let components :=
    String.intercalate "," <|
      result.summaries.toList.mapIdx
        (representativeJson symmetry.horizontalMap symmetry.verticalMap
          componentCount)
  let directedEdgeCount :=
    result.summaries.foldl
      (fun total summary => total + summary.directedEdgeCount) 0
  "{\"meta\":{\"width\":4,\"height\":5" ++
    ",\"classicPositions\":" ++ statePositionsJson classic ++
    ",\"verticalClassicPositions\":" ++
      statePositionsJson (verticalMirrorState classic) ++
    ",\"shapeStateCount\":" ++ toString result.stateCount ++
    ",\"componentCount\":" ++ toString result.summaries.size ++
    ",\"horizontalComponentOrbitCount\":" ++
      toString (componentOrbitCount symmetry.horizontalMap) ++
    ",\"kleinComponentOrbitCount\":" ++
      toString (kleinComponentOrbitCount
        symmetry.horizontalMap symmetry.verticalMap) ++
    ",\"horizontalFixedComponentCount\":" ++
      toString (fixedComponentCount symmetry.horizontalMap) ++
    ",\"verticalFixedComponentCount\":" ++
      toString (fixedComponentCount symmetry.verticalMap) ++
    ",\"rotationFixedComponentCount\":" ++
      toString (fixedComponentCount
        (symmetry.verticalMap.map fun vertical =>
          componentMapGet symmetry.horizontalMap vertical componentCount)) ++
    ",\"classicComponentId\":" ++ toString symmetry.classicId ++
    ",\"verticalClassicComponentId\":" ++
      toString symmetry.verticalClassicId ++
    ",\"coveredStateCount\":" ++ toString result.coveredCount ++
    ",\"directedEdgeCount\":" ++ toString directedEdgeCount ++
    ",\"allValid\":" ++ toString result.allValid ++
    ",\"keysUnique\":" ++ toString result.keysUnique ++
    ",\"closed\":" ++ toString result.closed ++
    ",\"equivalence\":\"finite_legal_slide_reachability\"" ++
    ",\"representativePolicy\":\"first_in_constructive_enumeration\"" ++
    "},\"components\":[" ++ components ++ "]}"

def main (args : List String) : IO UInt32 := do
  let output :=
    args.head?.getD "frontend/full-shape-components.json"
  IO.println "Enumerating all classic equal-shape placements and components..."
  IO.FS.writeFile output fullSpaceJson
  IO.println s!"Wrote {analyze.stateCount} states in {analyze.summaries.size} components to {output}"
  return 0
