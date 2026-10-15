import ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinateAt
import ComplexityOfGenerators.Simulation.SavitchMachine.SkipWorkPrefix
import ComplexityOfGenerators.Simulation.SavitchMachine.WorkWindowCorrectness

/-! Compose head decoding, work-window location and the finite cell scan into
an observation test. Both the selected head and every encoded work cell are
validated. The input stack is preserved on success and rejection. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.WorkObservation

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [Inhabited S]

inductive Label (symbols : ℕ)
  | copyCode | duplicateCode | read (pc : ReadCoordinateAt.Label)
  | skip (pc : SkipWorkPrefix.Label) | copyWindow | duplicateWindow | reset
  | window (pc : WorkWindow.Label symbols) | reject | done
  deriving DecidableEq, Fintype

def slots : Fin 4 ↪ Fin 7 := ⟨![1, 5, 2, 0], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

def program (write : Symbol → S) (read : S → Symbol) (states symbols : ℕ)
    (observed : Option (Fin symbols)) : Label symbols → Stmt S (Label symbols) (Status × Option S) 6
  | .copyCode => transferCode 0 3 .copyCode .duplicateCode (fun _ => true)
  | .duplicateCode => StackSpace.duplicateCode 3 0 1 .duplicateCode (.read (.skip .copy))
  | .read .done => .branch (fun v => v.1.returned.getD false)
      (.goto fun _ => .skip (.skip .copy)) (.goto fun _ => .reject)
  | .read pc => embedCode (Function.Embedding.refl _) Label.read
      (ReadCoordinateAt.program write read 2 (states + 3) pc)
  | .skip .done => .goto fun _ => .copyWindow
  | .skip pc => embedCode (Function.Embedding.refl _) Label.skip
      (SkipWorkPrefix.program (write (some false)) states pc)
  | .copyWindow => transferCode 1 3 .copyWindow .duplicateWindow (fun _ => true)
  | .duplicateWindow => StackSpace.duplicateCode 3 1 5 .duplicateWindow .reset
  | .reset => .load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .window (.loop false))
  | .window .done => .goto fun _ => .done
  | .window pc => embedCode slots Label.window
      (transportCode write read (Initialize.pack write) (Initialize.unpack read) (WorkWindow.program symbols observed none pc))
  | .reject => .load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .done)
  | .done => .halt

def test (states symbols n bound : ℕ) (observed : Option (Fin symbols)) (bits : List Bool) : Bool :=
  ((FixedWidthCodec.fin bound).decode ((bits.drop (2 * n + (states + 3))).take bound)).any fun head =>
    let window := bits.drop (2 * n + (states + 3) + bound)
    WorkWindow.test symbols observed none bound head.val false window window

/-- The whole observation check is a uniform finite program. The original
bitstream may be malformed; no branch expands a coordinate without its cap. -/
theorem run (write : Symbol → S) (read : S → Symbol) (inverse : Function.LeftInverse read write)
    (states symbols : ℕ) (observed : Option (Fin symbols)) (answer : Bool)
    (bits : List Bool) (input : List S) (bound r : ℕ)
    (bitsRoom : bits.length ≤ r) (inputRoom : input.length ≤ r)
    (offsetRoom : 2 * input.length + (states + 3) ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    ∃ stk,
      Trace (program write read states symbols observed) r
        (localConfig .copyCode (carrying answer false) (ReadCoordinateAt.before write bits [] bound input))
        (localConfig .done (carrying answer (test states symbols input.length bound observed bits)) stk) ∧
      stk 6 = input := by
  let P := program write read states symbols observed
  let source := (bits.map some).map write
  let original := ReadCoordinateAt.before write bits [] bound input
  have initial : ∀ j, (original j).length ≤ r := by
    intro j; fin_cases j <;> simp [original, ReadCoordinateAt.before] <;> omega
  have copied := copy_all P 3 0 1 .duplicateCode (.read (.skip .copy)) .copyCode rfl rfl
    (by decide) (by decide) (by decide) (carrying answer false) original rfl r initial (by
      simpa [original, ReadCoordinateAt.before] using bitsRoom)
  have copyLayout : Function.update original (1 : Fin 7) (original 0 ++ original 1) =
      ReadCoordinateAt.before write bits source bound input := by
    funext j; fin_cases j <;> simp [original, ReadCoordinateAt.before, source]
  rw [copyLayout] at copied
  obtain ⟨value, parsed, valueBound, exactValue⟩ := ReadCoordinateAt.run write read inverse 2 (states + 3)
    answer bits source input bound r bitsRoom (by simpa [source] using bitsRoom) inputRoom offsetRoom counterRoom
  have mapped := parsed.rename_active (by simp [localConfig]) Label.read P (by
    intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
  simp only [renameConfig, localConfig, Option.map_some] at mapped
  have first := copied.trans mapped
  let field := (bits.drop (2 * input.length + (states + 3))).take bound
  let window := bits.drop (2 * input.length + (states + 3) + bound)
  let parsedMemory := ReadCoordinateAt.after write value source bound input
  change Trace P r _ (localConfig (.read .done) (carrying answer ((FixedWidthCodec.fin bound).decode field).isSome) parsedMemory) at first
  cases decoded : (FixedWidthCodec.fin bound).decode field with
  | none =>
      simp only [decoded, Option.isSome_none] at first
      refine ⟨parsedMemory, ?_, rfl⟩
      have rejected : test states symbols input.length bound observed bits = false := by
        simp only [test, show (bits.drop (2 * input.length + (states + 3))).take bound = field from rfl, decoded, Option.any_none]
      rw [rejected]
      exact first.trans (.step first.end_bound rfl
        (.step first.end_bound (by simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying]) (.refl _ first.end_bound)))
  | some head =>
      have valueEq := exactValue head decoded
      subst value
      simp only [decoded, Option.isSome_some] at first
      have ready : TM2.step P (localConfig (.read .done) (carrying answer true) parsedMemory) =
          some (localConfig (.skip (.skip .copy)) (carrying answer true) parsedMemory) := rfl
      have skipped := (SkipWorkPrefix.run (write (some false)) states (carrying answer true)
        ((unary head.val).map write) source ((unary bound).map write) [] input r
        (by simp; omega) (by simpa [source] using bitsRoom) (by simp; omega) (by simp)
        inputRoom offsetRoom).rename_active (by simp [localConfig]) Label.skip P
          (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
      let workMemory := SkipWorkPrefix.registers ((unary head.val).map write)
        ((window.map some).map write) ((unary bound).map write) [] input
      change Trace P r (localConfig (.skip (.skip .copy)) (carrying answer true) parsedMemory)
        (localConfig (.skip .done) (carrying answer true)
          (SkipWorkPrefix.registers ((unary head.val).map write)
            (source.drop (2 * input.length + (states + 3) + ((unary bound).map write).length))
            ((unary bound).map write) [] input)) at skipped
      have workLayout : SkipWorkPrefix.registers ((unary head.val).map write)
          (source.drop (2 * input.length + (states + 3) + ((unary bound).map write).length))
          ((unary bound).map write) [] input = workMemory := by
        simp [source, window, workMemory]
      rw [workLayout] at skipped
      have copyWindow := copy_all P 3 1 5 .duplicateWindow .reset .copyWindow rfl rfl
        (by decide) (by decide) (by decide) (carrying answer true) workMemory rfl r skipped.end_bound (by
          dsimp [workMemory, SkipWorkPrefix.registers, window]
          simp
          omega)
      let both := SkipWorkPrefix.registers ((unary head.val).map write)
        ((window.map some).map write) ((unary bound).map write) ((window.map some).map write) input
      have bothLayout : Function.update workMemory (5 : Fin 7) (workMemory 1 ++ workMemory 5) = both := by
        funext j; fin_cases j <;> simp [workMemory, both, SkipWorkPrefix.registers]
      rw [bothLayout] at copyWindow
      obtain ⟨lastMemory, compared⟩ := WorkWindow.run symbols observed none answer bound head.val false window window r
        (by dsimp [window]; simp; omega) (by dsimp [window]; simp; omega) (by omega) (by omega)
      have reset : TM2.step P (localConfig .reset (carrying answer true) both) =
          some (localConfig (.window (.loop false)) (carrying answer false) both) := by
        simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying]
      have transported := Trace.transport write read (Initialize.pack write) (Initialize.unpack read)
        inverse (Initialize.pack_inverse write read inverse) compared
      have windowTrace := transported.embed_active (by simp [transportConfig, localConfig]) slots Label.window P
        (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl)) both copyWindow.end_bound
      have layout : Function.extend slots
          (fun j => (WorkWindow.registers window window bound head.val j).map write) both = both := by
        apply extend_eq
        · intro i; fin_cases i <;> rfl
        · intro j outside; rfl
      simp only [embedConfig, transportConfig, localConfig, Initialize.pack,
        Option.map_some, Option.map_none, layout] at windowTrace
      let finalMemory := Function.extend slots (fun j => (lastMemory j).map write) both
      have inputPreserved : finalMemory 6 = input := by
        have outside : ¬ ∃ i, slots i = (6 : Fin 7) := by
          simp [slots, Fin.exists_fin_succ]
        rw [show finalMemory 6 = both 6 from Function.extend_apply' _ _ _ outside]
        rfl
      have result : test states symbols input.length bound observed bits =
          WorkWindow.test symbols observed none bound head.val false window window := by
        simp only [test, show (bits.drop (2 * input.length + (states + 3))).take bound = field from rfl, decoded, Option.any_some]
        rfl
      refine ⟨finalMemory, ?_, inputPreserved⟩
      rw [result]
      have finalStep : TM2.step P (localConfig (.window .done)
          (carrying answer (WorkWindow.test symbols observed none bound head.val false window window)) finalMemory) =
          some (localConfig .done
            (carrying answer (WorkWindow.test symbols observed none bound head.val false window window)) finalMemory) := rfl
      exact first.trans (.step first.end_bound ready
        (skipped.trans (.step skipped.end_bound rfl
          (copyWindow.trans (.step copyWindow.end_bound reset (windowTrace.trans
            (.step windowTrace.end_bound finalStep (.refl _ windowTrace.end_bound))))))))

/-- The observation succeeds exactly when the work-head coordinate and
whole tape window decode and the selected cell has the requested symbol. -/
theorem test_correct (states symbols n bound : ℕ) (observed : Option (Fin symbols)) (bits : List Bool) :
    test states symbols n bound observed bits = true ↔
      ∃ head : Fin bound, ∃ cells : Fin bound → Option (Fin symbols),
        (FixedWidthCodec.fin bound).decode ((bits.drop (2 * n + (states + 3))).take bound) = some head ∧
        ((FixedWidthCodec.optionFin symbols).vector bound).decode
          (bits.drop (2 * n + (states + 3) + bound)) = some cells ∧ cells head = observed := by
  simp only [test, Option.any_eq_true]
  constructor
  · rintro ⟨head, decoded, accepted⟩
    obtain ⟨a, b, ha, hb, read, update⟩ :=
      (WorkWindow.test_correct symbols observed none bound head _ _).mp accepted
    exact ⟨head, a, decoded, ha, read⟩
  · rintro ⟨head, cells, decoded, window, observedAtHead⟩
    refine ⟨head, decoded, (WorkWindow.test_correct symbols observed none bound head _ _).mpr ?_⟩
    exact ⟨cells, cells, window, window, observedAtHead, by simp [WorkWindow.written]⟩

end ComplexityOfGenerators.Simulation.SavitchMachine.WorkObservation
