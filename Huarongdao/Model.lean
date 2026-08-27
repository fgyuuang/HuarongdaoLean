namespace Huarongdao

inductive Piece where
  | caoCao | guanYu | zhangFei | zhaoYun | maChao | huangZhong
  | soldier1 | soldier2 | soldier3 | soldier4
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

def Piece.all : List Piece :=
  [.caoCao, .guanYu, .zhangFei, .zhaoYun, .maChao, .huangZhong,
   .soldier1, .soldier2, .soldier3, .soldier4]

def Piece.index : Piece → Nat
  | .caoCao => 0 | .guanYu => 1 | .zhangFei => 2 | .zhaoYun => 3
  | .maChao => 4 | .huangZhong => 5 | .soldier1 => 6 | .soldier2 => 7
  | .soldier3 => 8 | .soldier4 => 9

def Piece.label : Piece → String
  | .caoCao => "曹操" | .guanYu => "关羽" | .zhangFei => "张飞"
  | .zhaoYun => "赵云" | .maChao => "马超" | .huangZhong => "黄忠"
  | .soldier1 => "兵一" | .soldier2 => "兵二" | .soldier3 => "兵三"
  | .soldier4 => "兵四"

structure Pos where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

structure Shape where
  width : Nat
  height : Nat
  deriving Repr, DecidableEq

def Piece.shape : Piece → Shape
  | .caoCao => ⟨2, 2⟩
  | .guanYu => ⟨2, 1⟩
  | .zhangFei | .zhaoYun | .maChao | .huangZhong => ⟨1, 2⟩
  | .soldier1 | .soldier2 | .soldier3 | .soldier4 => ⟨1, 1⟩

inductive Direction where
  | up | down | left | right
  deriving Repr, DecidableEq, BEq

def Direction.all : List Direction := [.up, .down, .left, .right]

def Direction.label : Direction → String
  | .up => "上" | .down => "下" | .left => "左" | .right => "右"

structure State where
  positions : Array Pos
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

def State.pos (s : State) (p : Piece) : Pos :=
  s.positions.getD p.index ⟨0, 0⟩

/-- Build the canonical ten-position array from a position function. -/
def State.ofFn (f : Piece → Pos) : State := ⟨#[
  f .caoCao, f .guanYu, f .zhangFei, f .zhaoYun, f .maChao,
  f .huangZhong, f .soldier1, f .soldier2, f .soldier3, f .soldier4
]⟩

@[simp] theorem State.ofFn_pos (f : Piece → Pos) (p : Piece) :
    (State.ofFn f).pos p = f p := by
  cases p <;> rfl

def occupiedCells (s : State) (p : Piece) : List Pos :=
  let origin := s.pos p
  let sh := p.shape
  (List.range sh.height).flatMap fun dy =>
    (List.range sh.width).map fun dx => ⟨origin.x + dx, origin.y + dy⟩

def inBounds (s : State) : Bool :=
  s.positions.size = Piece.all.length && Piece.all.all fun p =>
    let pos := s.pos p
    let sh := p.shape
    pos.x + sh.width ≤ 4 && pos.y + sh.height ≤ 5

def noOverlap (s : State) : Bool :=
  Piece.all.all fun p => Piece.all.all fun q =>
    p == q || (occupiedCells s p).all fun a =>
      (occupiedCells s q).all fun b => a != b

def valid (s : State) : Bool := inBounds s && noOverlap s

def ValidState (s : State) : Prop := valid s = true

def translated (pos : Pos) : Direction → Option Pos
  | .up => if pos.y = 0 then none else some ⟨pos.x, pos.y - 1⟩
  | .down => some ⟨pos.x, pos.y + 1⟩
  | .left => if pos.x = 0 then none else some ⟨pos.x - 1, pos.y⟩
  | .right => some ⟨pos.x + 1, pos.y⟩

def moveUnchecked (s : State) (p : Piece) (d : Direction) : Option State := do
  let next ← translated (s.pos p) d
  return State.ofFn fun q => if q = p then next else s.pos q

theorem moveUnchecked_pos {s next : State} {p q : Piece} {d : Direction}
    (h : moveUnchecked s p d = some next) :
    next.pos q = if q = p then (translated (s.pos p) d).getD (s.pos p) else s.pos q := by
  unfold moveUnchecked at h
  cases ht : translated (s.pos p) d with
  | none => simp [ht] at h
  | some pos =>
      simp [ht] at h
      subst next
      simp

def tryMove (s : State) (p : Piece) (d : Direction) : Option State := do
  let next ← moveUnchecked s p d
  if valid next then some next else none

theorem tryMove_pos {s next : State} {p q : Piece} {d : Direction}
    (h : tryMove s p d = some next) :
    next.pos q = if q = p then (translated (s.pos p) d).getD (s.pos p) else s.pos q := by
  unfold tryMove at h
  cases hm : moveUnchecked s p d with
  | none => simp [hm] at h
  | some candidate =>
      by_cases hv : valid candidate = true
      · simp [hm, hv] at h
        subst next
        exact moveUnchecked_pos hm
      · simp [hm, hv] at h

def legalMoves (s : State) : List (Piece × Direction × State) :=
  Piece.all.flatMap fun p => Direction.all.filterMap fun d =>
    (tryMove s p d).map fun next => (p, d, next)

def goal (s : State) : Bool := s.pos .caoCao == ⟨1, 3⟩

def classic : State := ⟨#[
  ⟨1, 0⟩, ⟨1, 2⟩,
  ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨3, 2⟩,
  ⟨1, 3⟩, ⟨2, 3⟩, ⟨0, 4⟩, ⟨3, 4⟩
]⟩

def Pos.code (pos : Pos) : Nat := pos.y * 4 + pos.x

def codesKey (codes : List Nat) : String :=
  String.intercalate "," (codes.mergeSort.map toString)

/-- Canonical key for the quotient by permutations of equal-shaped pieces. -/
def State.key (s : State) : String :=
  let cao := (s.pos .caoCao).code
  let guan := (s.pos .guanYu).code
  let vertical := [.zhangFei, .zhaoYun, .maChao, .huangZhong].map fun p => (s.pos p).code
  let soldiers := [.soldier1, .soldier2, .soldier3, .soldier4].map fun p => (s.pos p).code
  toString cao ++ ";" ++ toString guan ++ ";" ++ codesKey vertical ++ ";" ++ codesKey soldiers

theorem classic_valid : ValidState classic := by rfl

end Huarongdao
