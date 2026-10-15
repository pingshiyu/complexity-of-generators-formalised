import ComplexityOfGenerators.Simulation.SavitchMachine.WorkObservation
import ComplexityOfGenerators.Simulation.SavitchMachine.Endpoint
import ComplexityOfGenerators.Simulation.SavitchMachine.Alphabet

/-! Compare the two encoded work windows at a native transition. Only the cell
under the source head may change. All other cells, and both persistent input
and endpoint column, are checked or preserved by bounded stack routines. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.WorkRelation

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false
variable {α : Type}

inductive Label (symbols : ℕ)
  | copyCode | duplicateCode | read (pc : ReadCoordinateAt.Label)
  | source (pc : SkipWorkPrefix.Label) | moveHead | load (pc : Endpoint.Label)
  | target (pc : SkipWorkPrefix.Label) | reset | window (pc : WorkWindow.Label symbols)
  | reject | done
  deriving DecidableEq, Fintype

def targetSlots : Fin 7 ↪ Fin 8 := ⟨![5, 0, 2, 3, 4, 1, 6], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

def windowSlots : Fin 4 ↪ Fin 8 := ⟨![1, 0, 2, 5], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

def program (states symbols : ℕ) (observed : Option (Fin symbols)) (write : Option (Fin symbols)) :
    Label symbols → Stmt (Alphabet α) (Label symbols) (Status × Option (Alphabet α)) 7
  | .copyCode => transferCode 0 3 .copyCode .duplicateCode (fun _ => true)
  | .duplicateCode => StackSpace.duplicateCode 3 0 1 .duplicateCode (.read (.skip .copy))
  | .read .done => .branch (fun v => v.1.returned.getD false)
      (.goto fun _ => .source (.skip .copy)) (.goto fun _ => .reject)
  | .read pc => embedCode (Function.Embedding.refl _) Label.read
      (extendCode (ReadCoordinateAt.program Alphabet.write Alphabet.read 2 (states + 3) pc))
  | .source .done => .goto fun _ => .moveHead
  | .source pc => embedCode (Function.Embedding.refl _) Label.source
      (extendCode (SkipWorkPrefix.program (Alphabet.write (some false)) states pc))
  | .moveHead => transferCode 0 5 .moveHead (.load .load) (fun _ => true)
  | .load .done => .goto fun _ => .target (.skip .copy)
  | .load pc => embedCode (Function.Embedding.refl _) Label.load
      (Endpoint.program (Alphabet.write none) (fun s => (Alphabet.read s).isSome) pc)
  | .target .done => .goto fun _ => .reset
  | .target pc => embedCode targetSlots Label.target
      (SkipWorkPrefix.program (Alphabet.write (some false)) states pc)
  | .reset => .load (fun v => (carrying v.1.answer false, none)) (.goto fun _ => .window (.loop false))
  | .window .done => .goto fun _ => .done
  | .window pc => embedCode windowSlots Label.window
      (transportCode Alphabet.write Alphabet.read (Initialize.pack (Alphabet.write (α := α))) (Initialize.unpack (Alphabet.read (α := α)))
        (WorkWindow.program symbols observed write pc))
  | .reject => .load (fun v => (carrying v.1.answer false, none)) (.goto fun _ => .done)
  | .done => .halt

def test (states symbols n bound : ℕ) (observed : Option (Fin symbols))
    (write : Option (Fin symbols)) (u v : List Bool) : Bool :=
  ((FixedWidthCodec.fin bound).decode ((u.drop (2 * n + (states + 3))).take bound)).any fun head =>
    WorkWindow.test symbols observed write bound head.val false
      (u.drop (2 * n + (states + 3) + bound)) (v.drop (2 * n + (states + 3) + bound))

/-- Exact native work-window relation, rejecting malformed source heads and
malformed windows. Temporary registers remain bounded on rejected branches. -/
theorem run (states symbols : ℕ) (observed : Option (Fin symbols)) (write : Option (Fin symbols))
    (answer : Bool) (u v : List Bool) (input parents : List (Alphabet α)) (bound r : ℕ)
    (sourceRoom : u.length ≤ r) (inputRoom : input.length ≤ r)
    (columnRoom : v.length + 1 + parents.length ≤ r)
    (offsetRoom : 2 * input.length + (states + 3) ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    let column := (v.map some).map Alphabet.write ++ Alphabet.write none :: parents
    ∃ stk, Trace (program states symbols observed write) r
      (localConfig .copyCode (carrying answer false)
        (Fin.snoc (ReadCoordinateAt.before Alphabet.write u [] bound input) column))
      (localConfig .done (carrying answer (test states symbols input.length bound observed write u v)) stk) ∧
      stk 6 = input ∧ stk 7 = column := by
  let P := program (α := α) states symbols observed write
  let source := (u.map some).map (Alphabet.write (α := α))
  let column := (v.map some).map (Alphabet.write (α := α)) ++ Alphabet.write none :: parents
  let original : Fin 8 → List (Alphabet α) :=
    Fin.snoc (ReadCoordinateAt.before Alphabet.write u [] bound input) column
  have columnBound : column.length ≤ r := by
    simp only [column, List.length_append, List.length_map, List.length_cons]; omega
  have initial : ∀ j, (original j).length ≤ r := by
    intro j; fin_cases j <;> simp [original, ReadCoordinateAt.before, Fin.snoc, column] <;> omega
  have copied := copy_all P 3 0 1 .duplicateCode (.read (.skip .copy)) .copyCode rfl rfl
    (by decide) (by decide) (by decide) (carrying answer false) original (by simp [original, ReadCoordinateAt.before, Fin.snoc])
    r initial (by simpa [original, ReadCoordinateAt.before, Fin.snoc] using sourceRoom)
  have copyLayout : Function.update original (1 : Fin 8) (original 0 ++ original 1) =
      Fin.snoc (ReadCoordinateAt.before Alphabet.write u source bound input) column := by
    funext j; fin_cases j <;> simp [original, ReadCoordinateAt.before, source, Fin.snoc] <;> rfl
  rw [copyLayout] at copied
  obtain ⟨value, parsed, valueBound, exactValue⟩ := ReadCoordinateAt.run
    (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse 2 (states + 3) answer u source input bound r
    sourceRoom (by simpa [source] using sourceRoom) inputRoom offsetRoom counterRoom
  have mapped := (parsed.extend column columnBound).rename_active
    (by simp [extendConfig, localConfig]) Label.read P (by
      intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
  simp only [renameConfig, extendConfig, localConfig, Option.map_some] at mapped
  have first := copied.trans mapped
  let field := (u.drop (2 * input.length + (states + 3))).take bound
  let uw := u.drop (2 * input.length + (states + 3) + bound)
  let vw := v.drop (2 * input.length + (states + 3) + bound)
  let decodedMemory : Fin 8 → List (Alphabet α) :=
    Fin.snoc (ReadCoordinateAt.after Alphabet.write value source bound input) column
  change Trace P r _ (localConfig (.read .done)
    (carrying answer ((FixedWidthCodec.fin bound).decode field).isSome) decodedMemory) at first
  cases decoded : (FixedWidthCodec.fin bound).decode field with
  | none =>
      simp only [decoded, Option.isSome_none] at first
      have rejected : test states symbols input.length bound observed write u v = false := by
        simp only [test, show (u.drop (2 * input.length + (states + 3))).take bound = field from rfl,
          decoded, Option.any_none]
      refine ⟨decodedMemory, ?_, ?_, Fin.snoc_last _ _⟩
      · rw [rejected]
        exact first.trans (.step first.end_bound rfl
          (.step first.end_bound (by simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying])
            (.refl _ first.end_bound)))
      · simp [decodedMemory, ReadCoordinateAt.after, Fin.snoc]
  | some head =>
      have eq := exactValue head decoded
      subst value
      simp only [decoded, Option.isSome_some] at first
      have skipped := ((SkipWorkPrefix.run (Alphabet.write (α := α) (some false)) states (carrying answer true)
        ((unary head.val).map Alphabet.write) source ((unary bound).map Alphabet.write) [] input r
        (by simp; omega) (by simpa [source] using sourceRoom) (by simp; omega) (by simp)
        inputRoom offsetRoom).extend column columnBound).rename_active
          (by simp [extendConfig, localConfig]) Label.source P (by
            intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
      simp only [renameConfig, extendConfig, localConfig, Option.map_some] at skipped
      let workMemory : Fin 8 → List (Alphabet α) :=
        ![(unary head.val).map Alphabet.write, (uw.map some).map Alphabet.write,
          (unary bound).map Alphabet.write, [], [], [], input, column]
      have sourceLayout : Fin.snoc
          (SkipWorkPrefix.registers ((unary head.val).map (Alphabet.write (α := α)))
            (source.drop (2 * input.length + (states + 3) + ((unary bound).map (Alphabet.write (α := α))).length))
            ((unary bound).map Alphabet.write) [] input) column = workMemory := by
        funext j; fin_cases j <;> simp [workMemory, SkipWorkPrefix.registers, source, uw, Fin.snoc] <;> rfl
      rw [sourceLayout] at skipped
      have moved := transfer_all P 0 5 (by decide) .moveHead (.load .load) (fun _ => true) rfl
        (carrying answer true) workMemory (by simp) r skipped.end_bound (by simp [workMemory]; omega)
      let ready : Fin 8 → List (Alphabet α) :=
        ![[], (uw.map some).map Alphabet.write, (unary bound).map Alphabet.write,
          [], [], (unary head.val).map Alphabet.write, input, column]
      have moveLayout : replaceTwo workMemory (0 : Fin 8) 5 [] ((workMemory 0).reverse ++ workMemory 5) = ready := by
        funext j; fin_cases j <;> simp [replaceTwo, workMemory, ready, List.map_reverse]
      rw [moveLayout] at moved
      have loaded := Endpoint.run (Alphabet.write (α := α) none) (fun s => (Alphabet.read s).isSome)
        (carrying answer true) ready ((v.map some).map Alphabet.write) parents rfl
        (by intro s hs; simp only [List.mem_map] at hs; rcases hs with ⟨s, hs, rfl⟩
            rcases hs with ⟨bit, hb, rfl⟩; rfl) rfl rfl rfl rfl r moved.end_bound
      have second := loaded.rename_active (by simp [localConfig]) Label.load P (by
        intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
      simp only [renameConfig, localConfig, Option.map_some] at second
      let targetReady := Function.update ready (0 : Fin 8) ((v.map some).map Alphabet.write)
      have targetSkip := (SkipWorkPrefix.run (Alphabet.write (α := α) (some false)) states (carrying answer true)
        ((unary head.val).map Alphabet.write) ((v.map some).map Alphabet.write)
        ((unary bound).map Alphabet.write) ((uw.map some).map Alphabet.write) input r
        (by simp; omega) (by simp; omega) (by simp; omega) (by dsimp [uw]; simp; omega)
        inputRoom offsetRoom).embed_active (by simp [localConfig]) targetSlots Label.target P
        (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl)) targetReady second.end_bound
      let both : Fin 8 → List (Alphabet α) :=
        ![(vw.map some).map Alphabet.write, (uw.map some).map Alphabet.write,
          (unary bound).map Alphabet.write, [], [], (unary head.val).map Alphabet.write, input, column]
      have targetStart : Function.extend targetSlots
          (SkipWorkPrefix.registers ((unary head.val).map (Alphabet.write (α := α))) ((v.map some).map Alphabet.write)
            ((unary bound).map Alphabet.write) ((uw.map some).map Alphabet.write) input) targetReady = targetReady := by
        apply extend_eq
        · intro i; fin_cases i <;> simp [targetSlots, targetReady, ready, SkipWorkPrefix.registers]
        · intro j outside; rfl
      have targetEnd : Function.extend targetSlots
          (SkipWorkPrefix.registers ((unary head.val).map (Alphabet.write (α := α)))
            (((v.map some).map Alphabet.write).drop
              (2 * input.length + (states + 3) + ((unary bound).map (Alphabet.write (α := α))).length))
            ((unary bound).map Alphabet.write) ((uw.map some).map Alphabet.write) input) targetReady = both := by
        apply extend_eq
        · intro i; fin_cases i <;> simp [targetSlots, both, SkipWorkPrefix.registers, vw]
        · intro j outside; fin_cases j <;>
            simp_all [targetSlots, Fin.exists_fin_succ, both, targetReady, ready]
      simp only [embedConfig, localConfig, Option.map_some, targetStart, targetEnd] at targetSkip
      obtain ⟨final, compared⟩ := WorkWindow.run symbols observed write answer bound head.val false uw vw r
        (by dsimp [uw]; simp; omega) (by dsimp [vw]; simp; omega) (by omega) (by omega)
      have transported := Trace.transport (Alphabet.write (α := α)) Alphabet.read (Initialize.pack (Alphabet.write (α := α)))
        (Initialize.unpack (Alphabet.read (α := α))) Alphabet.inverse (Initialize.pack_inverse (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse) compared
      have last := transported.embed_active (by simp [transportConfig, localConfig]) windowSlots Label.window P
        (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl)) both targetSkip.end_bound
      have windowLayout : Function.extend windowSlots
          (fun j => (WorkWindow.registers uw vw bound head.val j).map (Alphabet.write (α := α))) both = both := by
        apply extend_eq
        · intro i; fin_cases i <;> rfl
        · intro j outside; rfl
      simp only [embedConfig, transportConfig, localConfig, Initialize.pack,
        Option.map_some, Option.map_none, windowLayout] at last
      let finalMemory := Function.extend windowSlots (fun j => (final j).map (Alphabet.write (α := α))) both
      have result : test states symbols input.length bound observed write u v =
          WorkWindow.test symbols observed write bound head.val false uw vw := by
        simp only [test, show (u.drop (2 * input.length + (states + 3))).take bound = field from rfl,
          decoded, Option.any_some]
        rfl
      refine ⟨finalMemory, ?_, ?_, ?_⟩
      · rw [result]
        exact first.trans (.step first.end_bound rfl (skipped.trans
          (.step skipped.end_bound rfl (moved.trans (second.trans
            (.step second.end_bound rfl (targetSkip.trans (.step targetSkip.end_bound rfl
              (.step targetSkip.end_bound (by simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying])
                (last.trans (.step last.end_bound rfl (.refl _ last.end_bound))))))))))))
      · have outside : ¬ ∃ i, windowSlots i = (6 : Fin 8) := by simp [windowSlots, Fin.exists_fin_succ]
        rw [show finalMemory 6 = both 6 from Function.extend_apply' _ _ _ outside]
        rfl
      · have outside : ¬ ∃ i, windowSlots i = (7 : Fin 8) := by simp [windowSlots, Fin.exists_fin_succ]
        rw [show finalMemory 7 = both 7 from Function.extend_apply' _ _ _ outside]
        rfl

end ComplexityOfGenerators.Simulation.SavitchMachine.WorkRelation
