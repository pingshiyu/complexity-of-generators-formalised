import ComplexityOfGenerators.Examples.SATNative.ParserRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeParser

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem header_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (header (O := O)).cost s ≤ 50 * (budget + 1) :=
  NativeHeader.headerRoutine_cost (s ∘ subslots) budget (by intro j; exact sizes (subslots j))

theorem header_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound (budget + 1) ((header (O := O)).eval s) := by
  have localBound := NativeHeader.headerRoutine_bound (O := O) (s ∘ subslots) budget
    (by intro j; exact sizes (subslots j))
  intro j
  by_cases member : ∃ i, subslots i = j
  · obtain ⟨i, rfl⟩ := member
    change (((NativeHeader.headerRoutine (O := O)).rename subslots).eval s (subslots i)).length ≤ _
    rw [Routine.rename_eval_here]
    exact localBound i
  · change (((NativeHeader.headerRoutine (O := O)).rename subslots).eval s j).length ≤ _
    rw [Routine.rename_eval_frame _ _ _ _ (by intro i equal; exact member ⟨i, equal.symm⟩)]
    exact (sizes j).trans (by omega)

theorem assign_bound {O : Type} (src dst scratch : Fin 32) (sd : src ≠ dst) (st : src ≠ scratch)
    (dt : dst ≠ scratch) (f : Symbol → Symbol) (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget ((Routine.assign (O := O) src dst scratch sd st dt f).eval s) := by
  intro j
  rw [Routine.assign_eval]
  by_cases target : j = dst
  · subst j
    simpa using sizes src
  · by_cases temporary : j = scratch
    · subst j
      simp [target]
    · simpa [Function.update_apply, target, temporary] using sizes j

theorem bodySetup_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget ((bodySetup (O := O)).eval s) := by
  have first := assign_bound (O := O) 5 10 9 (by decide) (by decide) (by decide) id s budget sizes
  have second := assign_bound (O := O) 2 16 9 (by decide) (by decide) (by decide) (fun _ => .one) _ budget first
  intro j
  simp only [bodySetup, Routine.seq, Routine.clearMany_eval]
  split_ifs
  · simp
  · exact second j

theorem assign_cost {O : Type} (src dst scratch : Fin 32) (sd : src ≠ dst) (st : src ≠ scratch)
    (dt : dst ≠ scratch) (f : Symbol → Symbol) (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (Routine.assign (O := O) src dst scratch sd st dt f).cost s ≤ 20 * budget + 3 := by
  rw [Routine.assign_cost]
  have a := sizes src
  have b := sizes dst
  have c := sizes scratch
  omega

theorem bodySetup_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (bodySetup (O := O)).cost s ≤ 60 * (budget + 1) := by
  let first := (Routine.assign (O := O) 5 10 9 (by decide) (by decide) (by decide) id).eval s
  let second := (Routine.assign (O := O) 2 16 9 (by decide) (by decide) (by decide) (fun _ => .one)).eval first
  have firstBound := assign_bound (O := O) 5 10 9 (by decide) (by decide) (by decide) id s budget sizes
  have secondBound := assign_bound (O := O) 2 16 9 (by decide) (by decide) (by decide) (fun _ => .one) first budget firstBound
  have one := assign_cost (O := O) 5 10 9 (by decide) (by decide) (by decide) id s budget sizes
  have two := assign_cost (O := O) 2 16 9 (by decide) (by decide) (by decide) (fun _ => .one) first budget firstBound
  have clearing := Routine.clearMany_cost (O := O) [17, 18] second budget (by intro j _; exact secondBound j)
  simp only [List.length_cons, List.length_nil] at clearing
  change (Routine.assign (O := O) 5 10 9 _ _ _ id).cost s + 1 +
    ((Routine.assign (O := O) 2 16 9 _ _ _ (fun _ => .one)).cost first + 1 +
    (Routine.clearMany (O := O) [17, 18]).cost second) ≤ _
  omega

/-- A polynomial primitive runtime is proved for the actual complete parser,
including malformed inputs. Native one-tape compilation is a separate, proved
quadratic simulation in `WordStack.InputBank.Native`. -/
theorem parser_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (parser (O := O)).cost s ≤ (stepConstant + 120) * (budget + 2)^2 := by
  let first := (header (O := O)).eval s
  let second := (bodySetup (O := O)).eval first
  have headerSize := header_bound (O := O) s budget sizes
  have setupSize := bodySetup_bound (O := O) first (budget + 1) headerSize
  have fields := header_fields (O := O) s
  dsimp only at fields
  obtain ⟨represented, clock⟩ := bodySetup_represents (O := O) first
    (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count (NativeHeader.parsedState (s 2)).word
    (NativeHeader.parsedState (s 2)).valid fields.1 fields.2.1 fields.2.2.1 fields.2.2.2
  have headerSizes := NativeHeader.parsedState_bounds (s 2)
  have capSizes := readOnes_lengths (s 2)
  have inputSize := sizes 2
  have capacity : (readOnes (s 2)).1 ≤ budget + 1 := by omega
  have active : (NativeHeader.parsedState (s 2)).count + 1 ≤ budget + 1 := by omega
  have one := header_cost (O := O) s budget sizes
  have two := bodySetup_cost (O := O) first (budget + 1) headerSize
  have three := NativeBody.bodyRoutine_cost (O := O) _ _ _ second represented (budget + 1) (by omega) setupSize capacity active
  have clockBound : (second 16).length ≤ budget := by rw [clock]; omega
  have bodyCost : (NativeBody.bodyRoutine (O := O)).cost second ≤
      budget * ((stepConstant + 4) * (budget + 2)) := by
    exact three.trans (Nat.mul_le_mul_right _ clockBound)
  change (header (O := O)).cost s + 1 +
    ((bodySetup (O := O)).cost first + 1 + (NativeBody.bodyRoutine (O := O)).cost second) ≤ _
  nlinarith [Nat.zero_le (stepConstant * (budget + 2))]

set_option maxHeartbeats 800000 in
theorem parser_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound (budget + 1) ((parser (O := O)).eval s) := by
  let first := (header (O := O)).eval s
  have headerSize := header_bound (O := O) s budget sizes
  have setupSize := bodySetup_bound (O := O) first (budget + 1) headerSize
  have fields := header_fields (O := O) s
  dsimp only at fields
  obtain ⟨represented, _⟩ := bodySetup_represents (O := O) first
    (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count (NativeHeader.parsedState (s 2)).word
    (NativeHeader.parsedState (s 2)).valid fields.1 fields.2.1 fields.2.2.1 fields.2.2.2
  have counts := NativeHeader.parsedState_bounds (s 2)
  have capacity := readOnes_lengths (s 2)
  have source := sizes 2
  exact NativeBody.bodyRoutine_bound (O := O) (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count
    ⟨(NativeHeader.parsedState (s 2)).word, false, false, (NativeHeader.parsedState (s 2)).valid⟩
    ((bodySetup (O := O)).eval first) represented (budget + 1) (by omega) setupSize (by omega) (by omega)

end ComplexityOfGenerators.Examples.PaddedCNF.NativeParser
