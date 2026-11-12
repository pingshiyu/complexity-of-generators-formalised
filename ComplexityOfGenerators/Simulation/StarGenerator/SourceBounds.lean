import ComplexityOfGenerators.Simulation.StarGenerator.Views
import ComplexityOfGenerators.Simulation.StarGenerator.TableBounds
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Bounds

set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

namespace ComplexityOfGenerators.Simulation.StarGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

theorem held_length_le (value : Option (List α)) (limit : ℕ)
    (valid : ∀ word, value = some word → word.length ≤ limit) :
    (UnionGenerator.held G G value).length ≤ limit := by
  cases value with
  | none => simp [UnionGenerator.held]
  | some word => simpa [UnionGenerator.held, UnionGenerator.letters] using valid word rfl

theorem sourceSetup_bound (s : Store G) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap) :
    StoreBound ((sourceSetup G).eval s) cap ∧ (sourceSetup G).cost s ≤ 70 * (cap + 1) := by
  let r := (readEntry G).eval s
  let f := (UnionGenerator.flag G G 27 false).eval r
  obtain ⟨rSize, rCost⟩ := readEntry_bound G s cap sizes positive
  obtain ⟨fSize, fCost⟩ := UnionGenerator.flag_bound G G 27 false r cap rSize positive
  obtain ⟨aSize, aCost⟩ := ConcatenationGenerator.assign_bound G G 24 13 33
    (by decide) (by decide) (by decide) f cap fSize
  refine ⟨aSize, ?_⟩
  change (readEntry G).cost s + 1 + ((UnionGenerator.flag G G 27 false).cost r + 1 +
    (WordStack.Routine.assign (O := α) 24 13 33 (by decide) (by decide) (by decide) id).cost f) ≤ _
  omega

theorem sourceSetup_index (s : Store G) : (sourceSetup G).eval s 24 = s 24 :=
  sourceSetup_fixes G 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s

theorem advance_bound (s : Store G) (cap : ℕ) (sizes : StoreBound s cap)
    (index : (s 24).length + 1 ≤ cap) :
    StoreBound ((advance G).eval s) cap ∧ (advance G).cost s = 3 := by
  have a := sizes.update 17 (s 17).tail (by
    simpa only [List.length_tail] using (Nat.sub_le (s 17).length 1).trans (sizes 17))
  have b := a.update 24 (Symbol.unit :: s 24) (by simpa using index)
  exact ⟨by simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push] using b, rfl⟩

noncomputable def stepBudget (seed time : PolynomialBound) (n cap : ℕ) : ℕ :=
  ((Source.body G (Symbol.left : Source.Symbol G → Cell G) (UnionGenerator.leftDecode G G)
    (Source.bank BoundedSource.sourceSlots)).bound + 500) * (cap + 1) +
      Command.counterBudget seed n + Command.counterBudget time n

theorem innerStep_bound (seed time : PolynomialBound) (table : Table α) (m j n cap : ℕ)
    (p : Option (List α) × BitString) (s : Store G) (stored : InnerStored G table m j p s)
    (tableBound : BoundedAt n (time n) table)
    (sizes : StoreBound s cap) (positive : 1 ≤ j) (jBound : j ≤ m) (mBound : m ≤ n)
    (indexBudget : n + 1 ≤ cap) (seedBudget : seed n ≤ cap) (timeBudget : time n + 1 ≤ cap)
    (sourceSpace : 1 + n + seed n + 3 * (time n + 1) ≤ cap) (wordBudget : n * time n ≤ cap) :
    StoreBound ((innerStep G seed time).eval s) cap ∧
      (innerStep G seed time).cost s ≤ stepBudget G seed time n cap := by
  let a := (sourceSetup G).eval s
  let old := (table.reverse.drop (j - 1)).head?.bind id
  obtain ⟨aSize, aCost⟩ := sourceSetup_bound G s cap sizes (by omega)
  have initial := sourceSetup_stored G table m j p s stored
  have aInput : a 11 = [] := initial.input
  have aAuxiliary : a 12 = [] := initial.auxiliary
  have jn : j ≤ n := by omega
  have seeds := seed.monotone jn
  have times := time.monotone jn
  obtain ⟨sourceSize, _, sourceCost⟩ :=
    BoundedSource.sourceTrial_bound (O := α) (Symbol.unit : Cell G) Symbol.bit G Symbol.left
      (UnionGenerator.leftDecode G G) (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit)
      (UnionGenerator.leftBit G G) (fun _ => rfl) seed time a (generatorData j) p.2
      (by simp [aInput, generatorData]) (by simp [aAuxiliary, generatorData])
      initial.index initial.random initial.empty cap aSize
      (by simpa [generatorData] using (by omega : j + 1 ≤ cap))
      (by simpa [generatorData] using (by omega : seed j ≤ cap))
      (by simpa [generatorData] using (by omega : time j + 1 ≤ cap))
      (by simpa [generatorData] using (by omega : 1 + j + seed j + 3 * (time j + 1) ≤ cap))
  let b := (UnionGenerator.leftFinish G G).eval ((UnionGenerator.leftTrial G G seed time).eval a)
  obtain ⟨bSize, bCost⟩ := UnionGenerator.leftFinish_bound G G _ cap sourceSize (by omega)
  have source := UnionGenerator.leftStep_stored G G seed time j p.2 none old a initial
  have leftLength : (b 25).length ≤ time n := by
    have valueLength := held_length_le G (UnionGenerator.sourceValue G time j (p.2.take (seed j))) (time j)
      (fun word output => clocked_source_length G time j _ word output)
    exact (congrArg List.length source.leftWord).le.trans (valueLength.trans times)
  have rightLength : (b 26).length ≤ (m - j) * time n := by
    have lookup : old = (table[m - j]?).bind id := cursorValue_eq table m j stored.length positive jBound
    have valueLength := held_length_le G old ((m - j) * time n) (by
      intro word output
      exact tableBound (m - j) word (lookup.symm.trans output) (by omega))
    exact (congrArg List.length source.rightWord).le.trans valueLength
  have pairSpace : (b 25).length + (b 26).length ≤ cap := calc
    _ ≤ time n + (m - j) * time n := Nat.add_le_add leftLength rightLength
    _ = (m - j + 1) * time n := by ring
    _ ≤ n * time n := Nat.mul_le_mul_right _ (by omega)
    _ ≤ cap := wordBudget
  obtain ⟨offeredSize, offeredCost⟩ := ConcatenationGenerator.offerStored_bound G G b cap bSize (by omega) pairSpace
  let o := (ConcatenationGenerator.offerStored G G).eval b
  have index : (o 24).length = j := by
    have offered : o 24 = b 24 := offerStored_fixes G 24 (by decide) (by decide) (by decide) b
    have call : b 24 = a 24 := ConcatenationGenerator.leftStep_frame G G seed time a 24 (by decide) (by decide) (by decide)
    exact (congrArg List.length (offered.trans (call.trans (sourceSetup_index G s)))).trans stored.index
  obtain ⟨finalSize, finalCost⟩ := advance_bound G o cap offeredSize (by rw [index]; omega)
  refine ⟨finalSize, ?_⟩
  have sc := (Command.counterBudget seed).monotone jn
  have tc := (Command.counterBudget time).monotone jn
  change (UnionGenerator.leftTrial G G seed time).cost a ≤ _ at sourceCost
  change (UnionGenerator.leftFinish G G).cost ((UnionGenerator.leftTrial G G seed time).eval a) ≤ _ at bCost
  simp only [generatorData] at sourceCost
  change (sourceSetup G).cost s + 1 + ((UnionGenerator.leftTrial G G seed time).cost a + 1 +
    ((UnionGenerator.leftFinish G G).cost ((UnionGenerator.leftTrial G G seed time).eval a) + 1 +
    ((ConcatenationGenerator.offerStored G G).cost b + 1 + (advance G).cost o))) ≤ _
  dsimp only [stepBudget]
  simp only [Nat.add_mul, Nat.mul_add] at sourceCost ⊢
  omega

end ComplexityOfGenerators.Simulation.StarGenerator
