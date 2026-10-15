import ComplexityOfGenerators.Simulation.StackSpace.Copy

/-! Unary multiplication for polynomial rulers. A consuming outer counter
repeatedly copies a preserved factor onto the result stack. All counters and
partial results occupy tape cells; finite control contains no natural counter. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ}

def copies (word : List S) : ℕ → List S
  | 0 => []
  | n + 1 => copies word n ++ word

@[simp] theorem copies_length (word : List S) (n : ℕ) :
    (copies word n).length = n * word.length := by
  induction n with
  | zero => simp [copies]
  | succ n ih => simp [copies, ih, Nat.succ_mul]

@[simp] theorem copies_replicate (symbol : S) (width n : ℕ) :
    copies (List.replicate width symbol) n = List.replicate (n * width) symbol := by
  induction n with
  | zero => simp [copies]
  | succ n ih => simp only [copies, ih, Nat.succ_mul, List.replicate_add]

def multiplyScan (counter : Fin (k + 1)) (copy exit : Q) : Stmt S Q (V × Option S) k :=
  .pop counter (fun v s => (v.1, s))
    (.branch (fun v => v.2.isSome)
      (.load (fun v => (v.1, none)) (.goto fun _ => copy))
      (.load (fun v => (v.1, none)) (.goto fun _ => exit)))

variable [Inhabited S]

/-- Multiply the length of the outer counter by the length of a preserved
word. The temporary stack is empty on both sides, and the result is prepended
to the existing destination. -/
theorem multiply_trace (P : Q → Stmt S Q (V × Option S) k)
    (counter factor result scratch : Fin (k + 1))
    (cf : counter ≠ factor) (cr : counter ≠ result) (cs : counter ≠ scratch)
    (fr : factor ≠ result) (fs : factor ≠ scratch) (rs : result ≠ scratch)
    (scan copy duplicate exit : Q)
    (scanTable : P scan = multiplyScan counter copy exit)
    (copyTable : P copy = transferCode factor scratch copy duplicate (fun _ => true))
    (duplicateTable : P duplicate = duplicateCode scratch factor result duplicate scan)
    (v : V) (stk : Fin (k + 1) → List S) (empty : stk scratch = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (room : (stk counter).length * (stk factor).length + (stk result).length ≤ r) :
    Trace P r (localConfig scan v stk)
      (localConfig exit v (replaceTwo stk counter result []
        (copies (stk factor) (stk counter).length ++ stk result))) := by
  generalize hc : stk counter = word at *
  induction word generalizing stk with
  | nil =>
      have unchanged : Function.update stk counter [] = stk := by
        rw [← hc]; exact Function.update_eq_self _ _
      have next : TM2.step P (localConfig scan v stk) = some (localConfig exit v stk) := by
        simp [TM2.step, localConfig, scanTable, multiplyScan, TM2.stepAux, hc, unchanged]
      have finish : replaceTwo stk counter result [] (stk result) = stk := by
        rw [← hc]; exact replaceTwo_same stk counter result
      simpa only [List.length_nil, copies, List.nil_append, finish] using
        Trace.step (show Within r (localConfig scan v stk) from bound) next (.refl _ bound)
  | cons bit word ih =>
      let popped := Function.update stk counter word
      have poppedBound : ∀ j, (popped j).length ≤ r := by
        intro j
        by_cases h : j = counter
        · subst j
          have h := bound counter
          simp only [hc, List.length_cons] at h
          simp only [popped, Function.update_self]; omega
        · simpa only [popped, Function.update_of_ne h] using bound j
      have next : TM2.step P (localConfig scan v stk) = some (localConfig copy v popped) := by
        simp [TM2.step, localConfig, scanTable, multiplyScan, TM2.stepAux, hc, popped]
      have copying := copy_all P scratch factor result duplicate scan copy copyTable duplicateTable
        fs.symm rs.symm fr v popped (by simp [popped, cs.symm, empty]) r poppedBound (by
          simp only [popped, Function.update_of_ne cf.symm, Function.update_of_ne cr.symm]
          simp only [List.length_cons, Nat.succ_mul] at room
          omega)
      let middle := Function.update popped result (stk factor ++ stk result)
      have copying' : Trace P r (localConfig copy v popped) (localConfig scan v middle) := by
        simpa only [popped, Function.update_of_ne cf.symm, Function.update_of_ne cr.symm] using copying
      have tail := ih middle (by simp [middle, popped, rs.symm, cs.symm, empty])
        copying'.end_bound (by simp [middle, popped, cr]) (by
          simpa only [middle, popped, Function.update_of_ne fr, Function.update_of_ne cf.symm,
            Function.update_self, List.length_append, List.length_cons, Nat.succ_mul,
            Nat.add_assoc] using room)
      have finish : replaceTwo middle counter result [] (copies (middle factor) word.length ++ middle result) =
          replaceTwo stk counter result [] (copies (stk factor) (bit :: word).length ++ stk result) := by
        simp only [middle, popped, Function.update_of_ne fr, Function.update_of_ne cf.symm,
          Function.update_self, List.length_cons, copies, List.append_assoc]
        funext j
        by_cases hr : j = result <;> by_cases hc' : j = counter <;>
          simp [replaceTwo, hr, hc', cr]
      rw [finish] at tail
      exact .step bound next (copying'.trans tail)

end ComplexityOfGenerators.Simulation.StackSpace
