import ComplexityOfGenerators.Simulation.WordStack.Words

/-! Read a fixed unary budget of random bits into a word register. Source
trials can subsequently use this stored block without exhausting the outer
random tape. Short outer tapes halt by exhaustion. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Command

variable {S O : Type} {k : ℕ}

def collectBody (counter dst : Fin k) (encode : Bool → S) : Command S O k :=
  .random ((push dst (encode false)).seq (pop counter)) ((push dst (encode true)).seq (pop counter))

def collect (counter dst : Fin k) (encode : Bool → S) : Command S O k :=
  .loop counter (fun o => o.1.isSome) (collectBody counter dst encode)

def afterBit (counter dst : Fin k) (encode : Bool → S) (m : Memory S O k) (bit : Bool) : Memory S O k :=
  ((Program.readBit m).set dst (encode bit :: m.store dst)).set counter (m.store counter).tail

theorem collectBody_runs (counter dst : Fin k) (different : counter ≠ dst) (encode : Bool → S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) (bit : Bool)
    (lookup : bits[m.randomHead]? = some bit) :
    (collectBody counter dst encode).Runs n bits m 4 (.done (afterBit counter dst encode m bit)) := by
  have first := push_runs dst (encode bit) bits (Program.readBit m) bounded
  have last := pop_runs counter bits ((Program.readBit m).set dst (encode bit :: m.store dst)) bounded
  simp only [Memory.set_there _ _ different, Program.readBit] at last
  have body := Runs.seq _ _ _ _ 1 1 _ first last
  apply Runs.random m _ _ bit 3 _ lookup
  cases bit <;> exact body

def collected (counter dst : Fin k) (encode : Bool → S) (bits : BitString) (m : Memory S O k)
    (count : ℕ) : Memory S O k :=
  {((m.set counter []).set dst (((bits.drop m.randomHead).take count).reverse.map encode ++ m.store dst)) with
    randomHead := m.randomHead + count}

theorem collect_full (counter dst : Fin k) (different : counter ≠ dst) (encode : Bool → S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (available : m.randomHead + (m.store counter).length ≤ bits.length) :
    (collect counter dst encode).Runs n bits m (6 * (m.store counter).length)
      (.done (collected counter dst encode bits m (m.store counter).length)) := by
  generalize word_eq : m.store counter = word at available ⊢
  induction word generalizing m with
  | nil =>
    have same : m.set counter [] = m := by rw [← word_eq, Memory.set_self]
    have final : collected counter dst encode bits m 0 = m := by simp [collected, same]
    rw [List.length_nil, Nat.mul_zero, final]
    exact Runs.loop_stop m counter _ _ (by simp [observe, word_eq])
  | cons a word ih =>
    have inside : m.randomHead < bits.length := by simp only [List.length_cons] at available; omega
    let bit := bits[m.randomHead]
    let middle := afterBit counter dst encode m bit
    have middleHead : middle.randomHead = m.randomHead + 1 := rfl
    have middleWord : middle.store counter = word := by simp [middle, afterBit, word_eq]
    have body := collectBody_runs counter dst different encode bits m bounded bit (List.getElem?_eq_getElem inside)
    have rest := ih middle bounded middleWord (by simp only [middleHead, List.length_cons] at available ⊢; omega)
    have window : (bits.drop m.randomHead).take (word.length + 1) =
        bit :: (bits.drop (m.randomHead + 1)).take word.length := by
      rw [List.drop_eq_getElem_cons inside, List.take_succ_cons]
    have final : collected counter dst encode bits middle word.length =
        collected counter dst encode bits m (a :: word).length := by
      apply Configuration.ext <;> try rfl
      · simp only [collected, middleHead, List.length_cons]; omega
      · funext j
        by_cases hc : j = counter <;> by_cases hd : j = dst <;>
          simp_all [collected, middle, afterBit, Memory.set, Program.readBit, Function.update_apply,
            window, List.reverse_cons, List.map_append, List.append_assoc]
    rw [final] at rest
    have run := Runs.loop m middle counter (fun o => o.1.isSome) _ 4 (6 * word.length) _
      (by simp [observe, word_eq]) body rest
    convert run using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

theorem collect_short (counter dst : Fin k) (different : counter ≠ dst) (encode : Bool → S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n)
    (short : bits.length - m.randomHead < (m.store counter).length) :
    ∃ t ≤ 6 * (m.store counter).length + 1, (collect counter dst encode).Runs n bits m t .exhausted := by
  generalize word_eq : m.store counter = word at short ⊢
  induction word generalizing m with
  | nil => simp only [List.length_nil] at short; omega
  | cons a word ih =>
    by_cases inside : m.randomHead < bits.length
    · let bit := bits[m.randomHead]
      let middle := afterBit counter dst encode m bit
      have body := collectBody_runs counter dst different encode bits m bounded bit (List.getElem?_eq_getElem inside)
      obtain ⟨t, cost, rest⟩ := ih middle bounded (by simp [middle, afterBit, word_eq])
        (by simp only [middle, afterBit, Memory.set_random, Program.readBit, List.length_cons] at short ⊢; omega)
      refine ⟨1 + 4 + 1 + t, ?_, Runs.loop m middle counter _ _ 4 t .exhausted
        (by simp [observe, word_eq]) body rest⟩
      simp only [List.length_cons]; omega
    · refine ⟨1, by simp, ?_⟩
      exact Runs.loop_absent m counter _ _ 0 (by simp [observe, word_eq])
        (Runs.random_absent m _ _ (List.getElem?_eq_none (by omega)))

end ComplexityOfGenerators.Simulation.WordStack.Command
