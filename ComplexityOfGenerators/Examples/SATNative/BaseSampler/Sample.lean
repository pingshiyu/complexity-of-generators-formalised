import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Choice

namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler

open Simulation.WordStack
set_option backward.isDefEq.respectTransparency false

def decodeWords : ℕ → BitString → List Symbol
  | 0, _ => []
  | count + 1, bits => decodeSymbol (bits.take 4) :: decodeWords count (bits.drop 4)

@[simp] theorem decodeWords_length (count : ℕ) (bits : BitString) : (decodeWords count bits).length = count := by
  induction count generalizing bits <;> simp [decodeWords, *]

def encodeWords (word : List Symbol) : BitString := word.flatMap encodeSymbol

@[simp] theorem encodeWords_length (word : List Symbol) : (encodeWords word).length = 4 * word.length := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      change (encodeSymbol letter ++ encodeWords rest).length = _
      rw [List.length_append, encodeSymbol_length, ih, List.length_cons]
      omega

theorem decodeWords_encode (word : List Symbol) (tail : BitString) :
    decodeWords word.length (encodeWords word ++ tail) = word := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.length_cons, decodeWords, encodeWords, List.flatMap_cons, List.append_assoc]
      have width := encodeSymbol_length letter
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
        decode_encodeSymbol]
      simpa only [encodeWords] using congrArg (letter :: ·) ih

def sampleBody (counter dst : Fin 35) : Code :=
  (readLetter dst 4 []).seq (Command.pop counter)

def sample (counter dst : Fin 35) : Code :=
  .loop counter (fun observation => observation.1.isSome) (sampleBody counter dst)

def afterSymbol (counter dst : Fin 35) (bits : BitString) (m : Memory) : Memory :=
  (afterLetter dst [] 4 bits m).set counter (m.store counter).tail

theorem sampleBody_full (counter dst : Fin 35) (different : counter ≠ dst)
    (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (available : m.randomHead + 4 ≤ bits.length) :
    (sampleBody counter dst).Runs n bits m 7 (.done (afterSymbol counter dst bits m)) := by
  have first := readLetter_full dst 4 [] n bits m index available
  have second := Command.pop_runs counter bits (afterLetter dst [] 4 bits m) index
  simp only [afterLetter, Memory.set_there _ _ different] at second
  exact Command.Runs.seq m _ _ _ 5 1 _ first second

def sampled (counter dst : Fin 35) (count : ℕ) (bits : BitString) (m : Memory) : Memory :=
  {((m.set counter []).set dst ((decodeWords count (bits.drop m.randomHead)).reverse ++ m.store dst))
    with randomHead := m.randomHead + 4 * count}

theorem sample_full (counter dst : Fin 35) (different : counter ≠ dst)
    (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (available : m.randomHead + 4 * (m.store counter).length ≤ bits.length) :
    (sample counter dst).Runs n bits m (9 * (m.store counter).length)
      (.done (sampled counter dst (m.store counter).length bits m)) := by
  generalize counterEq : m.store counter = clock at available ⊢
  induction clock generalizing m with
  | nil =>
      have same : m.set counter [] = m := by rw [← counterEq, Memory.set_self]
      have final : sampled counter dst 0 bits m = m := by simp [sampled, same, decodeWords]
      rw [List.length_nil, Nat.mul_zero, final]
      exact Command.Runs.loop_stop m counter _ _ (by simp [observe, counterEq])
  | cons mark clock ih =>
      have enough : m.randomHead + 4 ≤ bits.length := by simp only [List.length_cons] at available; omega
      let middle := afterSymbol counter dst bits m
      have middleClock : middle.store counter = clock := by simp [middle, afterSymbol, counterEq]
      have middleHead : middle.randomHead = m.randomHead + 4 := rfl
      have body := sampleBody_full counter dst different n bits m index enough
      have rest := ih middle index middleClock (by
        simp only [middleHead, List.length_cons] at available ⊢
        omega)
      have window : bits.drop (m.randomHead + 4) = (bits.drop m.randomHead).drop 4 := by
        simp only [List.drop_drop, Nat.add_comm]
      have final : sampled counter dst clock.length bits middle =
          sampled counter dst (mark :: clock).length bits m := by
        apply Configuration.ext <;> try rfl
        · simp only [sampled, middleHead, List.length_cons]; omega
        · funext j
          by_cases counterCase : j = counter
          · subst j
            simp [sampled, middle, afterSymbol, afterLetter, Memory.set, different]
          · by_cases outputCase : j = dst
            · subst j
              simp [sampled, middle, afterSymbol, afterLetter, Memory.set, different.symm,
                decodeWords, List.reverse_cons, List.append_assoc, List.drop_drop, Nat.add_comm]
            · simp [sampled, middle, afterSymbol, afterLetter, Memory.set, counterCase, outputCase]

      rw [final] at rest
      have run := Command.Runs.loop m middle counter (fun observation => observation.1.isSome) _
        7 (9 * clock.length) _ (by simp [observe, counterEq]) body rest
      convert run using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

theorem sample_short (counter dst : Fin 35) (different : counter ≠ dst)
    (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (randomBound : m.randomHead ≤ bits.length)
    (short : bits.length < m.randomHead + 4 * (m.store counter).length) :
    ∃ ticks ≤ 9 * (m.store counter).length + 5,
      (sample counter dst).Runs n bits m ticks .exhausted := by
  generalize counterEq : m.store counter = clock at short ⊢
  induction clock generalizing m with
  | nil => simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at short
           omega
  | cons mark clock ih =>
      by_cases enough : m.randomHead + 4 ≤ bits.length
      · let middle := afterSymbol counter dst bits m
        have body := sampleBody_full counter dst different n bits m index enough
        obtain ⟨ticks, bound, rest⟩ := ih middle index (by exact enough) (by simp [middle, afterSymbol, counterEq]) (by
          simp only [middle, afterSymbol, afterLetter, Memory.set_random, List.length_cons] at short ⊢
          omega)
        refine ⟨1 + 7 + 1 + ticks, ?_, Command.Runs.loop m middle counter _ _ 7 ticks .exhausted
          (by simp [observe, counterEq]) body rest⟩
        simp only [List.length_cons] at bound ⊢
        omega
      · obtain ⟨ticks, bound, absent⟩ := readLetter_short dst 4 [] n bits m index randomBound (by omega)
        exact ⟨1 + ticks, by simp only [List.length_cons]; omega,
          Command.Runs.loop_absent m counter _ _ ticks (by simp [observe, counterEq])
            (Command.Runs.seq_absent m _ _ ticks absent)⟩

end ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler
