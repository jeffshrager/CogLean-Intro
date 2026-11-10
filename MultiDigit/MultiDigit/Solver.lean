/-
The column backup as problem solving (CogLib `Process/ProblemSolving`).

The state of a partly worked problem: the next column (0 units, 1 tens,
2 hundreds, 3 past the hundreds), the carry into it, the column's sum once
it is known, what has been written in each column so far (units first;
a cell may hold no digit, one, or two), and whether work has stopped.

Operators (the problem space):
* `add i`: add column `i`'s digits by the single-digit process (`fact`,
  e.g. a DOA trial) and the carry into it. Precondition: it is column `i`
  and its sum is not yet known.
* `write i`: write the sum. Precondition: it is a single digit.
* `writeCarry i`: write the sum's units digit and carry its tens into the
  next column. Precondition: the sum is known.
* `finish`: at the end, write any final carry. Precondition: past the
  hundreds.
* Repairs (Brown & VanLehn 1980, §2.6, carried over to addition): `skip i`
  (leave the cell blank), `quit`, `writeUnits i` (write only the sum's
  rightmost digit: a refocus onto part of the sum), `writeBoth i` (write
  both digits of the sum in the cell).

The procedure (decision-cycle rules), `full`: add a column, then write its
units and carry; at the end, finish. The repairs are offered by `heuristics`
and, with no critics (`lenient`), never arise, because `full` meets no
impasse.

Result:
* `bridge`: the full procedure gives exactly the old column backup,
  `columns`, for every problem and every single-digit process. So every
  MultiDigit theorem about the backup holds for the problem solver.

The lab edition (github.com/jeffshrager/CogLean) carries the rest: the
procedure without the carry rule, the four repair bugs of 15 + 17, and
means-ends analysis over the same space.
-/

import MultiDigit.Columns
import CogLib.Process.ProblemSolving

namespace MD.Solver

open Cog

/-- The place of a column. -/
def placeOf : Nat → Place
  | 0 => .units
  | 1 => .tens
  | _ => .hundreds

/-- The state of a partly worked problem. -/
structure St where
  p : Problem
  col : Nat
  carry : Nat
  sum : Option Nat
  out : List (List Nat)
  done : Bool
  deriving DecidableEq

inductive Op
  | add (i : Nat) | write (i : Nat) | writeCarry (i : Nat) | finish
  | skip (i : Nat) | quit | writeUnits (i : Nat) | writeBoth (i : Nat)
  deriving DecidableEq

def init (p : Problem) : St := ⟨p, 0, 0, none, [], false⟩

/-- Move on to the next column, having written `cell` and carrying `c`. -/
def next (s : St) (cell : List Nat) (c : Nat) : St :=
  { s with col := s.col + 1, carry := c, sum := none, out := s.out ++ [cell] }

/-- At the end: write any final carry, and stop. -/
def finishSt (s : St) : St :=
  { s with out := s.out ++ (if s.carry = 0 then [] else [[s.carry]]), done := true }

/-- The problem space, with `fact` the single-digit process. -/
def space (fact : Nat → Nat → Dist Nat) : Space St Op where
  pre o s := match o with
    | .add i => s.col == i && i < 3 && s.sum.isNone && !s.done
    | .write i => s.col == i && (match s.sum with | some v => v < 10 | none => false)
    | .writeCarry i | .skip i | .writeUnits i | .writeBoth i => s.col == i && s.sum.isSome
    | .finish => s.col == 3 && !s.done
    | .quit => !s.done
  apply o s := match o, s.sum with
    | .add i, _ => Dist.bind (fact (s.p.digit .first (placeOf i)) (s.p.digit .second (placeOf i)))
        fun r => Dist.pure { s with sum := some (r + s.carry) }
    | .write _, some v => Dist.pure (next s [v] 0)
    | .writeCarry _, some v => Dist.pure (next s [v % 10] (v / 10))
    | .writeUnits _, some v => Dist.pure (next s [v % 10] 0)
    | .writeBoth _, some v => Dist.pure (next s (if v < 10 then [v] else [v / 10, v % 10]) 0)
    | .skip _, some _ => Dist.pure (next s [] 0)
    | .finish, _ => Dist.pure (finishSt s)
    | .quit, _ => Dist.pure { s with done := true }
    | _, _ => Dist.pure s

/-- The full procedure. -/
def full : Procedure St Op := fun s =>
  if s.done then none
  else if s.col < 3 then (if s.sum.isNone then some (.add s.col) else some (.writeCarry s.col))
  else some .finish

/-- The repair heuristics: at a stuck `write`, skip, quit, write the units
digit, or write both digits. -/
def heuristics : Op → St → List Op
  | .write i, _ => [.skip i, .quit, .writeUnits i, .writeBoth i]
  | _, _ => []

/-- No critics. -/
def lenient : Repairer St Op := ⟨heuristics, fun _ _ => false⟩

/-- The value of what is written: cells read as one number, units first; a
blank cell is a blank position. -/
def readOut : List (List Nat) → Nat → Nat
  | [], _ => 0
  | ds :: rest, m => ds.foldl (fun a d => a * 10 + d) 0 * m + readOut rest (m * 10 ^ max 1 ds.length)

def answer (s : St) : Nat := readOut s.out 1

/-- The answers a procedure gives. -/
def answers (fact : Nat → Nat → Dist Nat) (P : Procedure St Op) (R : Repairer St Op) (p : Problem) :
    Dist Nat :=
  Dist.bind (run (space fact) P R 8 (init p)) fun s => Dist.pure (answer s)

/-! ### The bridge -/

/-- Unfold one step of the run where no impasse arises. -/
theorem run_step (fact : Nat → Nat → Dist Nat) (P : Procedure St Op) (R : Repairer St Op) (k : Nat)
    (s : St) (o : Op) (hp : P s = some o) (hpre : (space fact).pre o s = true) :
    run (space fact) P R (k + 1) s =
      Dist.bind ((space fact).apply o s) fun s' => run (space fact) P R k s' := by
  simp only [run, step_no_impasse _ P R s o hp hpre, Dist.bind_assoc, Dist.bind_pure_left]

theorem run_stop (fact : Nat → Nat → Dist Nat) (P : Procedure St Op) (R : Repairer St Op) (k : Nat)
    (s : St) (hp : P s = none) : run (space fact) P R (k + 1) s = Dist.pure s := by
  simp only [run, step, hp, Dist.bind_pure_left]

theorem apply_add (fact : Nat → Nat → Dist Nat) (i : Nat) (s : St) :
    (space fact).apply (.add i) s =
      Dist.bind (fact (s.p.digit .first (placeOf i)) (s.p.digit .second (placeOf i)))
        fun r => Dist.pure { s with sum := some (r + s.carry) } := rfl

theorem apply_writeCarry (fact : Nat → Nat → Dist Nat) (i v : Nat) (s : St) (h : s.sum = some v) :
    (space fact).apply (.writeCarry i) s = Dist.pure (next s [v % 10] (v / 10)) := by
  simp [space, h]

theorem apply_finish (fact : Nat → Nat → Dist Nat) (s : St) :
    (space fact).apply .finish s = Dist.pure (finishSt s) := by
  simp only [space]

/-- The full procedure, unfolded: three facts, then the written answer. -/
theorem run_full (fact : Nat → Nat → Dist Nat) (p : Problem) :
    run (space fact) full lenient 8 (init p) =
      Dist.bind (fact (p.digit .first .units) (p.digit .second .units)) fun r0 =>
      Dist.bind (fact (p.digit .first .tens) (p.digit .second .tens)) fun r1 =>
      Dist.bind (fact (p.digit .first .hundreds) (p.digit .second .hundreds)) fun r2 =>
        let s0 := r0
        let s1 := r1 + s0 / 10
        let s2 := r2 + s1 / 10
        let c3 := s2 / 10
        Dist.pure ⟨p, 3, c3, none, [[s0 % 10], [s1 % 10], [s2 % 10]] ++
          (if c3 = 0 then [] else [[c3]]), true⟩ := by
  rw [show (8 : Nat) = 7 + 1 from rfl, run_step fact full lenient 7 _ (.add 0) rfl rfl, apply_add]
  simp only [init, placeOf, Dist.bind_assoc, Dist.bind_pure_left, Nat.add_zero]
  apply Dist.bind_congr; intro r0
  rw [show (7 : Nat) = 6 + 1 from rfl, run_step fact full lenient 6 _ (.writeCarry 0) rfl rfl,
    apply_writeCarry fact 0 r0 _ rfl, Dist.bind_pure_left]
  rw [show (6 : Nat) = 5 + 1 from rfl, run_step fact full lenient 5 _ (.add 1) rfl rfl, apply_add]
  simp only [next, placeOf, Dist.bind_assoc, Dist.bind_pure_left]
  apply Dist.bind_congr; intro r1
  rw [show (5 : Nat) = 4 + 1 from rfl, run_step fact full lenient 4 _ (.writeCarry 1) rfl rfl,
    apply_writeCarry fact 1 _ _ rfl, Dist.bind_pure_left]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_step fact full lenient 3 _ (.add 2) rfl rfl, apply_add]
  simp only [next, placeOf, Dist.bind_assoc, Dist.bind_pure_left]
  apply Dist.bind_congr; intro r2
  rw [show (3 : Nat) = 2 + 1 from rfl, run_step fact full lenient 2 _ (.writeCarry 2) rfl rfl,
    apply_writeCarry fact 2 _ _ rfl, Dist.bind_pure_left]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_step fact full lenient 1 _ .finish rfl rfl, apply_finish,
    Dist.bind_pure_left]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_stop fact full lenient 0 _ rfl]
  simp [next, finishSt]

/-- **The bridge**: the full procedure answers exactly as the column backup
`columns` does, for every problem and every single-digit process. -/
theorem bridge (fact : Nat → Nat → Dist Nat) (p : Problem) :
    answers fact full lenient p = columns fact p := by
  rw [answers, run_full, columns_place_value]
  simp only [Dist.bind_assoc, Dist.bind_pure_left]
  apply Dist.bind_congr; intro r0
  apply Dist.bind_congr; intro r1
  apply Dist.bind_congr; intro r2
  congr 1
  simp only [answer]
  by_cases h : (r2 + (r1 + r0 / 10) / 10) / 10 = 0 <;>
    simp [h, readOut, List.foldl] <;> omega

end MD.Solver
