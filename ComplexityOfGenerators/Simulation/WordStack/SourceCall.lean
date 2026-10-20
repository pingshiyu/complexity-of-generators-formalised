import ComplexityOfGenerators.Simulation.WordStack.SourceInitialize
import ComplexityOfGenerators.Simulation.WordStack.SourceBounds
import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops

namespace ComplexityOfGenerators.Simulation.WordStack.Source

variable {I A O S Output : Type} {k : ℕ} (M : Machine I A O)

theorem outside_bank (slots : Layout k) (j : Fin 17) (outside : 11 ≤ j.val) :
    ∀ i, slots j ≠ bank slots i := by
  intro i eq
  have same := congrArg (fun x : Fin 17 => x.val) (slots.injective eq)
  dsimp at same
  omega

noncomputable def call [Fintype S] (slots : Layout k) (encode : Symbol M → S) (decode : S → Symbol M)
    (f g b : S → S) : Routine S Output k :=
  (prepare slots (encode (.state (.live M.initial))) f g b (encode .unit)).seq
    (Routine.clocked (slots 16) (body M encode decode (bank slots))
      (fun s => Local.rename_frame (bank slots) _ s (slots 16) (outside_bank slots 16 (by decide))))

theorem prepare_clock (slots : Layout k) (state unit : S) (f g b : S → S) (s : Local.Store S k) :
    (prepare (Output := Output) slots state f g b unit).eval s (slots 16) = s (slots 16) := by
  simpa using prepare_external (Output := Output) slots state unit f g b s (slots 16)
    (outside_bank slots 16 (by decide))

theorem call_bank [Fintype S] (slots : Layout k) (encode : Symbol M → S) (decode : S → Symbol M)
    (retract : Function.LeftInverse decode encode) (f g b : S → S)
    (s : Local.Store S k) (data : InputData I A) (bits : BitString)
    (input_eq : (s (slots 11)).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s (slots 12)).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s (slots 13)).length = data.index)
    (bits_eq : (s (slots 14)).reverse.map b = bits.map (fun a => encode (.bit a))) :
    (call (Output := Output) M slots encode decode f g b).eval s ∘ bank slots =
      Local.mapStore encode
        (((Snapshot.step M)^[(s (slots 16)).length] (initial M data bits)).store M) := by
  let prepared := (prepare (Output := Output) slots (encode (.state (.live M.initial))) f g b (encode .unit)).eval s
  have start := prepare_initial (Output := Output) M slots encode f g b s data bits
    input_eq auxiliary_eq index_eq bits_eq
  have iter (t : ℕ) :
      ((Local.counted (slots 16) (body M encode decode (bank slots))).eval^[t] prepared) ∘ bank slots =
        Local.mapStore encode (((Snapshot.step M)^[t] (initial M data bits)).store M) := by
    induction t with
    | zero => exact start
    | succ t ih =>
      simpa only [Function.iterate_succ_apply'] using
        counted_eval M encode decode retract (bank slots) (slots 16)
          (fun i => (outside_bank slots 16 (by decide) i).symm) _ _ ih
  simpa only [call, Routine.seq, Routine.clocked, prepare_clock] using iter (s (slots 16)).length

theorem call_frame [Fintype S] (slots : Layout k) (encode : Symbol M → S) (decode : S → Symbol M)
    (f g b : S → S) (s : Local.Store S k) (j : Fin k)
    (outside : ∀ i, j ≠ bank slots i) (clock : j ≠ slots 16) :
    (call (Output := Output) M slots encode decode f g b).eval s j =
      if j = slots 14 ∨ j = slots 15 then [] else s j := by
  let c := Local.counted (slots 16) (body M encode decode (bank slots))
  have fixed (store : Local.Store S k) : c.eval store j = store j := by
    change (body M encode decode (bank slots)).eval ((Local.pop (slots 16)).eval store) j = store j
    rw [body, Local.rename_frame _ _ _ _ outside, Local.eval_pop, Function.update_of_ne clock]
  have iter (t : ℕ) (store : Local.Store S k) : (c.eval^[t] store) j = store j := by
    induction t with
    | zero => rfl
    | succ t ih => simpa only [Function.iterate_succ_apply', fixed] using ih
  change (c.eval^[_] _) j = _
  rw [iter]
  exact prepare_external slots _ _ f g b s j outside

theorem call_cost [Fintype S] (slots : Layout k) (encode : Symbol M → S) (decode : S → Symbol M)
    (f g b : S → S) (s : Local.Store S k) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (call (Output := Output) M slots encode decode f g b).cost s ≤
      ((body M encode decode (bank slots)).bound + 105) * (budget + 1) := by
  have setup := prepare_cost (Output := Output) slots (encode (.state (.live M.initial))) (encode .unit) f g b s budget sizes
  have clock := sizes (slots 16)
  simp only [call, Routine.seq, Routine.clocked, prepare_clock]
  nlinarith

theorem call_clock [Fintype S] (slots : Layout k) (encode : Symbol M → S) (decode : S → Symbol M)
    (f g b : S → S) (s : Local.Store S k) :
    (call (Output := Output) M slots encode decode f g b).eval s (slots 16) = [] := by
  exact Routine.iterate_clock (slots 16) (Routine.ofLocal (O := Output) (body M encode decode (bank slots)))
    (fun store => Local.rename_frame (bank slots) _ store (slots 16) (outside_bank slots 16 (by decide))) _

theorem call_size [Fintype S] (slots : Layout k) (encode : Symbol M → S) (decode : S → Symbol M)
    (retract : Function.LeftInverse decode encode) (f g b : S → S)
    (s : Local.Store S k) (data : InputData I A) (bits : BitString)
    (input_eq : (s (slots 11)).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s (slots 12)).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s (slots 13)).length = data.index)
    (bits_eq : (s (slots 14)).reverse.map b = bits.map (fun a => encode (.bit a)))
    (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) (j : Fin k) :
    ((call (Output := Output) M slots encode decode f g b).eval s j).length ≤ 7 * budget + 1 := by
  have inputLength := congrArg List.length input_eq
  have auxLength := congrArg List.length auxiliary_eq
  have bitsLength := congrArg List.length bits_eq
  simp only [List.length_map, List.length_reverse] at inputLength auxLength bitsLength
  by_cases inside : ∃ i, bank slots i = j
  · obtain ⟨i, rfl⟩ := inside
    have projection := congrFun (call_bank (Output := Output) M slots encode decode retract f g b s data bits
      input_eq auxiliary_eq index_eq bits_eq) i
    rw [Function.comp_apply] at projection
    rw [projection]
    simp only [Local.mapStore, List.length_map]
    apply (Snapshot.store_length_le M _ i).trans
    apply (Snapshot.iterate_size M _ _).trans
    rw [initial_size]
    have h₁ := sizes (slots 11)
    have h₂ := sizes (slots 12)
    have h₃ := sizes (slots 13)
    have h₄ := sizes (slots 14)
    have h₅ := sizes (slots 16)
    omega
  · by_cases clock : j = slots 16
    · subst j
      rw [call_clock]
      simp
    · have outside : ∀ i, j ≠ bank slots i := by intro i eq; exact inside ⟨i, eq.symm⟩
      rw [call_frame M slots encode decode f g b s j outside clock]
      split
      · simp
      · exact (sizes j).trans (by omega)

theorem call_size_of_bound [Fintype S] (slots : Layout k) (encode : Symbol M → S) (decode : S → Symbol M)
    (retract : Function.LeftInverse decode encode) (f g b : S → S)
    (s : Local.Store S k) (data : InputData I A) (bits : BitString)
    (input_eq : (s (slots 11)).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s (slots 12)).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s (slots 13)).length = data.index)
    (bits_eq : (s (slots 14)).reverse.map b = bits.map (fun a => encode (.bit a)))
    (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget)
    (space : 1 + data.input.length + data.auxiliary.length + data.index + bits.length +
      3 * (s (slots 16)).length ≤ budget) (j : Fin k) :
    ((call (Output := Output) M slots encode decode f g b).eval s j).length ≤ budget := by
  by_cases inside : ∃ i, bank slots i = j
  · obtain ⟨i, rfl⟩ := inside
    have projection := congrFun (call_bank (Output := Output) M slots encode decode retract f g b s data bits
      input_eq auxiliary_eq index_eq bits_eq) i
    rw [Function.comp_apply] at projection
    rw [projection]
    simp only [Local.mapStore, List.length_map]
    apply (Snapshot.store_length_le M _ i).trans
    apply (Snapshot.iterate_size M _ _).trans
    simpa only [initial_size] using space
  · by_cases clock : j = slots 16
    · subst j
      rw [call_clock]
      simp
    · have outside : ∀ i, j ≠ bank slots i := by intro i eq; exact inside ⟨i, eq.symm⟩
      rw [call_frame M slots encode decode f g b s j outside clock]
      split
      · simp
      · exact sizes j

end ComplexityOfGenerators.Simulation.WordStack.Source
