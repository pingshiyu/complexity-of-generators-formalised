import ComplexityOfGenerators.Simulation.WordStack.Words

/-! Unary counters built using primitive stack commands. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Command

variable {S O : Type} {k : ℕ}

def loadIndex (dst : Fin k) (unit : S) : Command S O k :=
  .loop dst (fun o => o.2.isSome) (.act dst (.push unit) .right none)

def loadedIndex (dst : Fin k) (unit : S) (n : ℕ) (m : Memory S O k) : Memory S O k :=
  {m.set dst (List.replicate (n - m.indexHead) unit ++ m.store dst) with indexHead := n}

theorem loadIndex_runs (dst : Fin k) (unit : S) (n : ℕ) (bits : BitString)
    (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    (loadIndex dst unit).Runs n bits m (3 * (n - m.indexHead)) (.done (loadedIndex dst unit n m)) := by
  generalize equation : n - m.indexHead = remaining
  induction remaining generalizing m with
  | zero =>
    have equal : m.indexHead = n := by omega
    have final : loadedIndex dst unit n m = m := by
      apply Configuration.ext <;> simp [loadedIndex, equal]
    rw [final]
    exact Runs.loop_stop m dst _ _ (by simp [observe, equal])
  | succ remaining ih =>
    have inside : m.indexHead < n := by omega
    let middle := Program.changeMemory dst n (.push unit) .right none m
    have middleHead : middle.indexHead = m.indexHead + 1 := by
      simp [middle, Program.changeMemory, Move.onInput, Nat.min_eq_left (by omega : m.indexHead + 1 ≤ n)]
    have rest := ih middle (by rw [middleHead]; omega) (by rw [middleHead]; omega)
    have final : loadedIndex dst unit n middle = loadedIndex dst unit n m := by
      have difference : n - m.indexHead = (n - middle.indexHead) + 1 := by omega
      apply Configuration.ext <;> simp only [loadedIndex, Memory.set, middle, Program.changeMemory,
        Action.apply, Option.toList_none, List.append_nil, Function.update_idem]
      funext j
      by_cases same : j = dst
      · subst j
        simp only [Function.update_self]
        rw [difference]
        simp [List.replicate_add, List.append_assoc, middleHead, Move.onInput,
          Nat.min_eq_left (by omega : m.indexHead + 1 ≤ n)]
      · simp [same]
    rw [final] at rest
    have run := Runs.loop m middle dst (fun o => o.2.isSome) (.act dst (.push unit) .right none)
      1 (3 * remaining) _ (by simp [observe, inside]) (Runs.act m dst (.push unit) .right none) rest
    convert run using 1 <;> first | rfl | omega

/-- A fixed constant is part of the finite program, not a runtime word literal. -/
def prepend (dst : Fin k) : List S → Command S O k
  | [] => .skip
  | a :: rest => (prepend dst rest).seq (push dst a)

theorem prepend_runs (dst : Fin k) (word : List S) {n : ℕ} (bits : BitString)
    (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    (prepend dst word).Runs n bits m (2 * word.length) (.done (m.set dst (word ++ m.store dst))) := by
  induction word with
  | nil => simpa [prepend] using Runs.skip m
  | cons a word ih =>
    have last := push_runs dst a bits (m.set dst (word ++ m.store dst)) bounded
    simp only [Memory.set_here, Memory.set_twice] at last
    have run := Runs.seq _ _ _ _ _ _ _ ih last
    convert run using 1 <;> rfl

def repeatWord (word : List S) : ℕ → List S
  | 0 => []
  | n + 1 => repeatWord word n ++ word

@[simp] theorem repeatWord_length (word : List S) (n : ℕ) :
    (repeatWord word n).length = n * word.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord, ih, Nat.add_mul]

@[simp] theorem repeatWord_replicate (unit : S) (a b : ℕ) :
    repeatWord (List.replicate b unit) a = List.replicate (a * b) unit := by
  induction a with
  | zero => simp [repeatWord]
  | succ a ih =>
    rw [repeatWord, ih, ← List.replicate_add]
    congr 1
    ring

/-- Consume a counter, prepending one copy of `base` per symbol to `dst`.
The base and empty scratch stack are restored after every iteration. -/
def multiply (counter base dst scratch : Fin k) : Command S O k :=
  .loop counter (fun o => o.1.isSome) ((pop counter).seq (copy base dst scratch id))

theorem multiply_runs (counter base dst scratch : Fin k)
    (cb : counter ≠ base) (cd : counter ≠ dst) (cs : counter ≠ scratch)
    (bd : base ≠ dst) (bs : base ≠ scratch) (ds : dst ≠ scratch)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (empty : m.store scratch = []) :
    (multiply counter base dst scratch).Runs n bits m
      ((m.store counter).length * (14 * (m.store base).length + 5))
      (.done ((m.set counter []).set dst (repeatWord (m.store base) (m.store counter).length ++ m.store dst))) := by
  generalize word_eq : m.store counter = word
  induction word generalizing m with
  | nil =>
    have final : (m.set counter []).set dst (repeatWord (m.store base) 0 ++ m.store dst) = m := by
      simp only [repeatWord, List.nil_append]
      rw [← word_eq, Memory.set_self, Memory.set_self]
    rw [List.length_nil, Nat.zero_mul, final]
    exact Runs.loop_stop m counter _ _ (by simp [observe, word_eq])
  | cons a word ih =>
    let middle := (m.set counter word).set dst (m.store base ++ m.store dst)
    have first := pop_runs counter bits m bounded
    simp only [word_eq, List.tail_cons] at first
    have last := copy_runs base dst scratch bd bs ds id bits (m.set counter word) bounded
      (by simp [cs.symm, empty])
    simp only [Memory.set_there _ _ cb.symm, Memory.set_there _ _ cd.symm, List.map_id] at last
    have body := Runs.seq m (m.set counter word) _ _ 1 (14 * (m.store base).length + 1) (.done middle) first last
    have rest := ih middle (by simpa [middle] using bounded)
      (by simp [middle, ds.symm, cs.symm, empty]) (by simp [middle, cd])
    have final : (middle.set counter []).set dst (repeatWord (middle.store base) word.length ++ middle.store dst) =
        (m.set counter []).set dst (repeatWord (m.store base) (a :: word).length ++ m.store dst) := by
      apply Configuration.ext <;> try rfl
      funext j
      by_cases hc : j = counter <;> by_cases hd : j = dst <;>
        simp_all [middle, Memory.set, Function.update_apply, repeatWord, List.append_assoc, cb.symm]
    rw [final] at rest
    have run := Runs.loop m middle counter (fun o => o.1.isSome) _
      (1 + 1 + (14 * (m.store base).length + 1))
      (word.length * (14 * (middle.store base).length + 5)) _ (by simp [observe, word_eq]) body rest
    convert run using 1
    · rfl
    · simp only [List.length_cons, middle, Memory.set_there _ _ bd, Memory.set_there _ _ cb.symm]
      ring

def scale (value base temp scratch : Fin k) : Command S O k :=
  (multiply value base temp scratch).seq (transfer temp value id)

theorem scale_runs (value base temp scratch : Fin k)
    (vb : value ≠ base) (vt : value ≠ temp) (vs : value ≠ scratch)
    (bt : base ≠ temp) (bs : base ≠ scratch) (ts : temp ≠ scratch)
    (unit : S) (a b : ℕ) {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (value_eq : m.store value = List.replicate a unit) (base_eq : m.store base = List.replicate b unit)
    (temp_eq : m.store temp = []) (scratch_eq : m.store scratch = []) :
    (scale value base temp scratch).Runs n bits m (a * (20 * b + 5) + 1)
      (.done (m.set value (List.replicate (a * b) unit))) := by
  let middle := (m.set value []).set temp (List.replicate (a * b) unit)
  have first := multiply_runs value base temp scratch vb vt vs bt bs ts bits m bounded scratch_eq
  simp only [value_eq, base_eq, List.length_replicate, repeatWord_replicate, temp_eq, List.append_nil] at first
  have last := transfer_runs temp value vt.symm id bits middle (by simpa [middle] using bounded)
  have final : (middle.set temp []).set value ((middle.store temp).reverse.map id ++ middle.store value) =
      m.set value (List.replicate (a * b) unit) := by
    apply Configuration.ext <;> try rfl
    funext j
    by_cases hv : j = value <;> by_cases ht : j = temp <;>
      simp_all [middle, Memory.set, Function.update_apply]
  rw [final] at last
  have run := Runs.seq _ _ _ _ _ _ _ first last
  convert run using 1
  · rfl
  · simp only [middle, Memory.set_here, List.length_replicate]
    ring

def power (value base temp scratch : Fin k) : ℕ → Command S O k
  | 0 => .skip
  | degree + 1 => (power value base temp scratch degree).seq (scale value base temp scratch)

def powerTime (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | degree + 1 => powerTime a b degree + a * b ^ degree * (20 * b + 5) + 2

theorem power_runs (value base temp scratch : Fin k)
    (vb : value ≠ base) (vt : value ≠ temp) (vs : value ≠ scratch)
    (bt : base ≠ temp) (bs : base ≠ scratch) (ts : temp ≠ scratch)
    (unit : S) (a b degree : ℕ) {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (value_eq : m.store value = List.replicate a unit) (base_eq : m.store base = List.replicate b unit)
    (temp_eq : m.store temp = []) (scratch_eq : m.store scratch = []) :
    (power value base temp scratch degree).Runs n bits m (powerTime a b degree)
      (.done (m.set value (List.replicate (a * b ^ degree) unit))) := by
  induction degree with
  | zero => simpa [power, powerTime, ← value_eq] using Runs.skip m
  | succ degree ih =>
    have last := scale_runs value base temp scratch vb vt vs bt bs ts unit (a * b ^ degree) b bits
      (m.set value (List.replicate (a * b ^ degree) unit)) bounded (by simp)
      (by simp [vb.symm, base_eq]) (by simp [vt.symm, temp_eq]) (by simp [vs.symm, scratch_eq])
    simp only [Memory.set_twice] at last
    have run := Runs.seq _ _ _ _ _ _ _ ih last
    convert run using 1
    · rfl
    · simp only [powerTime]; ring
    · simp only [pow_succ, Nat.mul_assoc]

theorem powerTime_bound (a b degree : ℕ) (positive : 1 ≤ b) :
    powerTime a b degree ≤ degree * (a * b ^ degree * (20 * b + 5) + 2) := by
  induction degree with
  | zero => simp [powerTime]
  | succ degree ih =>
    have power_le : b ^ degree ≤ b ^ (degree + 1) := by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ positive
    have term_le : a * b ^ degree * (20 * b + 5) ≤ a * b ^ (degree + 1) * (20 * b + 5) := by gcongr
    simp only [powerTime]
    calc
      powerTime a b degree + a * b ^ degree * (20 * b + 5) + 2 ≤
          degree * (a * b ^ (degree + 1) * (20 * b + 5) + 2) +
            (a * b ^ (degree + 1) * (20 * b + 5) + 2) := by
        have := Nat.mul_le_mul_left degree (Nat.add_le_add_right term_le 2)
        omega
      _ = _ := by ring

end ComplexityOfGenerators.Simulation.WordStack.Command
