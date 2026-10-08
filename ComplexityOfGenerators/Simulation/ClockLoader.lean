import ComplexityOfGenerators.Simulation.ClockInputReset
import ComplexityOfGenerators.Simulation.BlockMarker
import ComplexityOfGenerators.Simulation.RoutineExecution

/-!
# Blank-tape initialisation for the polynomial clock

The established native block loader writes the origin, one ordinary cell per
input symbol, and a right endpoint. The radix is consequently `inputLength + 2`;
the resulting clock budget is `p (inputLength + 1)`, a polynomial that dominates
`p inputLength`. A separate native scan restores the read-only input head.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

def machineRoutine {I A O : Type} (M : Machine I A O) : Routine I A O M.symbols where
  states := M.states
  initial := M.initial
  transition := M.transition

variable {I O : Type} [Fintype I] [Fintype O] (M : Machine I Bool O) (p : PolynomialBound)

def clockFirstCell : ClockCell M.symbols p.degree := ⟨none, true, false, fun _ => true, true⟩

def clockLastCell : ClockCell M.symbols p.degree := ⟨none, false, true, fun _ => false, false⟩

def clockBlocks : InputBlocks I (ClockCell M.symbols p.degree) where
  leading := [clockFirstCell M p]
  trailing := [clockLastCell M p]
  block := fun _ => [default]

omit [Fintype I] [Fintype O] in
@[simp] theorem clockBlocks_word (w : List I) :
    (clockBlocks M p).word w =
      clockFirstCell M p :: (List.replicate w.length default ++ [clockLastCell M p]) := by
  have flat : w.flatMap (fun _ => [default]) = List.replicate w.length (default : ClockCell M.symbols p.degree) := by
    induction w <;> simp_all [List.replicate_succ]
  simp [InputBlocks.word, clockBlocks, flat]

def clockLoaderProgram : Turing.TM0.Machine (ClockCell M.symbols p.degree) Unit := fun _ _ => none

def clockLoader : Machine I Bool Unit :=
  blockMachine (clockLoaderProgram M p) (Fintype.equivFin Unit) (clockAlphabet M p) (clockBlocks M p)

def clockPreparedLoader : Machine I Bool Unit :=
  sequenceMachine (clockLoader M p) (machineRoutine (clockInputReset M p))

/-- A native finite-control machine, starting on the standard blank work tape.
No clock, index, or source work tape is supplied externally. -/
def polynomialClockMachine : Machine I Bool O :=
  sequenceMachine (clockPreparedLoader M p) (polynomialClockRoutine M p)

omit [Fintype I] [Fintype O] in
theorem clock_initial_lookup (n j : ℕ) :
    (clockFirstCell M p :: (List.replicate n default ++ [clockLastCell M p])).getD j default =
      if j = 0 then clockFirstCell M p else if j = n + 1 then clockLastCell M p else default := by
  cases j with
  | zero => simp
  | succ j =>
      rw [List.getD_cons_succ]
      by_cases inside : j < n
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using inside)]
        simp [inside, show j ≠ n by omega]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using Nat.le_of_not_gt inside)]
        by_cases eq : j = n
        · subst j; simp
        · have pos : 0 < j - n := by omega
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt pos)
          simp [hk, eq]

omit [Fintype I] [Fintype O] in
theorem clock_initial_memory (n : ℕ) :
    PolynomialClockMemory M p (n + 1) (fun _ => none)
      (clockLocations (List.replicate p.degree 0)) (some 0)
      (bootMemory (clockAlphabet M p)
        (clockFirstCell M p :: (List.replicate n default ++ [clockLastCell M p])) (n + 2)) := by
  have digits : clockLocations (List.replicate p.degree 0) = fun _ : Fin p.degree => some (0 : ℤ) := by
    funext i
    simp [clockLocations, i.isLt]
  rw [digits]
  intro i
  by_cases marker : i = -1
  · subst i
    simp [bootMemory, clockRead, polynomialClockCell]
    rfl
  · by_cases inside : 0 ≤ i ∧ i < ((n + 2 : ℕ) : ℤ)
    · simp only [bootMemory, ite_eq_right marker, ite_eq_left inside, clockRead, bootDecode_encode]
      rw [clock_initial_lookup]
      have cast : (i.toNat : ℤ) = i := by omega
      by_cases first : i.toNat = 0
      · have zero : i = 0 := by omega
        subst i
        simp [clockFirstCell, polynomialClockCell]
        omega
      · by_cases last : i.toNat = n + 1
        · have atLast : i = ((n + 1 : ℕ) : ℤ) := by omega
          have nz : (n : ℤ) + 1 ≠ 0 := by omega
          simp [atLast, clockLastCell, polynomialClockCell, nz, Ne.symm nz]
        · have notOrigin : i ≠ 0 := by omega
          have notLast : i ≠ ((n + 1 : ℕ) : ℤ) := by omega
          simp only [ite_eq_right first, ite_eq_right last, polynomialClockCell,
            Option.some.injEq, notOrigin, Ne.symm notOrigin, notLast, decide_false]
          rfl
    · have notOrigin : i ≠ 0 := by omega
      have notLast : i ≠ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [bootMemory, ite_eq_right marker, ite_eq_right inside, clockRead,
        polynomialClockCell, Option.some.injEq, notOrigin, Ne.symm notOrigin, notLast, decide_false]
      rfl

end

end ComplexityOfGenerators.Simulation
