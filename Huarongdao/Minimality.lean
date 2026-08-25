import Huarongdao.ProofGame

namespace Huarongdao

/-- A ranking certificate turns local one-step inequalities into a global lower bound. -/
structure LowerBoundCertificate (start : State) (bound : Nat) where
  rank : State → Nat
  startRank : rank start = 0
  stepRank : ∀ {s t : State} {p : Piece} {d : Direction},
    tryMove s p d = some t → rank t ≤ rank s + 1
  goalRank : ∀ {t : State}, goal t = true → bound ≤ rank t

namespace LowerBoundCertificate

theorem path_rank_le_aux (rank : State → Nat)
    (stepRank : ∀ {s t : State} {p : Piece} {d : Direction},
      tryMove s p d = some t → rank t ≤ rank s + 1)
    (path : Path start target) :
    rank target ≤ rank start + path.length := by
  induction path with
  | nil => simp [Path.length]
  | cons action step tail ih =>
      have hstep := stepRank step
      simp only [Path.length]
      omega

theorem path_rank_le (certificate : LowerBoundCertificate start bound)
    (path : Path start target) :
    certificate.rank target ≤ certificate.rank start + path.length :=
  path_rank_le_aux certificate.rank certificate.stepRank path

theorem path_lower_bound (certificate : LowerBoundCertificate start bound)
    (path : Path start target) (hgoal : goal target = true) :
    bound ≤ path.length := by
  have hrank := certificate.path_rank_le path
  have hgoalRank := certificate.goalRank hgoal
  rw [certificate.startRank] at hrank
  omega

theorem solution_lower_bound (certificate : LowerBoundCertificate start bound)
    (solution : Solution start) : bound ≤ solution.length :=
  certificate.path_lower_bound solution.path solution.solved

end LowerBoundCertificate

/-- If a solution meets a certified lower bound exactly, it is minimal. -/
theorem Solution.minimal_of_certificate
    (solution : Solution start)
    (certificate : LowerBoundCertificate start solution.length) :
    solution.Minimal := by
  intro other
  exact certificate.solution_lower_bound other

/-- Executing a list of actions can raise the certified rank by at most its length. -/
theorem runMoves_rank_le_aux (rank : State → Nat)
    (stepRank : ∀ {s t : State} {p : Piece} {d : Direction},
      tryMove s p d = some t → rank t ≤ rank s + 1)
    {start target : State} {actions : List Action}
    (executed : runMoves start actions = some target) :
    rank target ≤ rank start + actions.length := by
  induction actions generalizing start with
  | nil =>
      simp [runMoves] at executed
      subst target
      simp
  | cons action rest ih =>
      cases hm : tryMove start action.piece action.direction with
      | none => simp [runMoves, hm] at executed
      | some next =>
          simp [runMoves, hm] at executed
          have tailRank := ih executed
          have headRank := stepRank hm
          simp only [List.length_cons]
          omega

theorem LowerBoundCertificate.runMoves_rank_le
    (certificate : LowerBoundCertificate start bound)
    {actions : List Action} {target : State}
    (executed : runMoves start actions = some target) :
    certificate.rank target ≤ certificate.rank start + actions.length :=
  runMoves_rank_le_aux certificate.rank certificate.stepRank executed

/-- The player's explicit action list inherits the same certified lower bound. -/
theorem LowerBoundCertificate.play_lower_bound
    (certificate : LowerBoundCertificate start bound)
    (play : CertifiedPlay start) : bound ≤ play.length := by
  have rankPath := certificate.runMoves_rank_le play.executed
  have goalRank := certificate.goalRank play.solved
  rw [certificate.startRank] at rankPath
  change bound ≤ play.actions.length
  omega

/-- A player completion meeting a certified lower bound is globally minimal. -/
theorem CertifiedPlay.minimal_of_certificate
    (play : CertifiedPlay start)
    (certificate : LowerBoundCertificate start play.length) :
    play.Minimal := by
  intro other
  exact certificate.play_lower_bound other

end Huarongdao
