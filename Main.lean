import Huarongdao

open Huarongdao

def main : IO Unit := do
  IO.println "Huarongdao Lean 4 formalization"
  IO.println s!"Classic layout valid: {valid classic}"
  IO.println s!"Initial legal moves: {(legalMoves classic).length}"
  for (piece, direction, next) in legalMoves classic do
    IO.println s!"  {piece.label} {direction.label} -> {next.key}"
