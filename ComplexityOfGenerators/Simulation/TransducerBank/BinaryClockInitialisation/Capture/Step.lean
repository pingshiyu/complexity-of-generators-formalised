import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

 theorem configuration_bounded (copies radius : ℕ) (data : InputData I A)
    (phase : Phase Q copies) (length temporary digits : List Bool) (inputPosition : ℕ)
    (counterPosition clockPosition : ℤ) (ctor : BankConfiguration Unit Q S k)
    (input : inputPosition≤data.input.length) (heads : ∀ j,(ctor.head j).natAbs≤radius)
    (counterBound : counterPosition.natAbs≤radius) (clockBound : clockPosition.natAbs≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).Bounded data radius
      (configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor) := by
  refine ⟨input,Nat.zero_le _,Nat.zero_le _,?_⟩
  intro j
  refine Fin.addCases (fun j=>?_) (fun j=>?_) j
  · simpa only [configuration,Fin.addCases_left] using heads j
  · refine Fin.cases ?_ (fun j=>?_) j
    · simpa only [configuration,Fin.addCases_right,Fin.cases_zero] using counterBound
    · simpa only [configuration,Fin.addCases_right,Fin.cases_succ] using clockBound

 theorem configuration_stay (copies : ℕ) (data : InputData I A)
    (phase next : Phase Q copies) (length temporary digits : List Bool) (inputPosition : ℕ)
    (counterPosition clockPosition : ℤ) (ctor : BankConfiguration Unit Q S k)
    (input : inputPosition≤data.input.length) :
    (bank (I:=I) (A:=A) (O:=O) C copies).advance data
      (configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor) next
      ((configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor).tape
        ((bank (I:=I) (A:=A) (O:=O) C copies).select phase)
        ((configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor).head
          ((bank (I:=I) (A:=A) (O:=O) C copies).select phase))) .stay .stay .stay .stay none =
      configuration (O:=O) C copies next length temporary digits inputPosition counterPosition clockPosition ctor := by
  simpa only [configuration] using TapeBank.advance_stay (bank (I:=I) (A:=A) (O:=O) C copies) data
    (configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor) next
    input (Nat.zero_le _) (Nat.zero_le _)

 theorem configuration_append (copies : ℕ) (data : InputData I A)
    (phase next : Phase Q copies) (length temporary digits : List Bool) (inputPosition : ℕ)
    (counterPosition : ℤ) (ctor : BankConfiguration Unit Q S k) (bit : Bool) (move : Move)
    (input : inputPosition≤data.input.length)
    (selected : (bank (I:=I) (A:=A) (O:=O) C copies).select phase=clock (k:=k)) :
    (bank (I:=I) (A:=A) (O:=O) C copies).advance data
      (configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition digits.length ctor) next
      (C.blank,((fun _=>none),some bit)) move .stay .stay .stay none =
      configuration (O:=O) C copies next length temporary (digits++[bit]) inputPosition counterPosition
        (move.onInt digits.length) ctor := by
  apply BankConfiguration.ext <;> try rfl
  case inputHead => simp [TapeBank.advance,configuration,Move.onInput,Nat.min_eq_left input]
  case head =>
    simp only [TapeBank.advance,configuration,selected,clock,Fin.addCases_right,Fin.cases_succ,BankEmbedding.update_right]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j=>?_) j
    · simp [Function.update]
    · have zero : j=0 := Fin.eq_zero j
      subst j
      simp only [Function.update_self]
      change move.onInt (digits.length:ℤ) = Fin.cases counterPosition
        (fun _ : Fin 1=>move.onInt (digits.length:ℤ)) (Fin.succ 0)
      rw [Fin.cases_succ]
  case tape =>
    simp only [TapeBank.advance,configuration,selected,clock,Fin.addCases_right,Fin.cases_succ,BankEmbedding.update_right]
    congr 1
    funext j p
    refine Fin.cases ?_ (fun j=>?_) j
    · simp [Function.update]
    · have zero : j=0 := Fin.eq_zero j
      subst j
      simp only [Function.update_self,Fin.cases_succ]
      have update := digitTape_write digits [] bit
      simp only [List.append_nil,List.tail_nil] at update
      by_cases same : p=(digits.length:ℤ)
      · subst p
        simpa only [Function.update_self] using congrArg (fun f=>(C.blank,((fun _ : Fin 3=>none),f (digits.length:ℤ)))) update
      · simpa only [Function.update_of_ne same] using
          congrArg (fun f=>(C.blank,((fun _ : Fin 3=>none),f p))) update

 theorem unary_input_map (word : List I) (position : ℕ) :
    word[position]?.map (fun _=>())=(List.replicate word.length ())[position]? := by
  rw [←List.getElem?_map]
  congr 1
  simp

 theorem constructor_instruction (copies : ℕ) (data : InputData I A)
    (length temporary digits : List Bool) (ctor : BankConfiguration Unit Q S k)
    (next write work input auxiliary index emit)
    (table : C.instruction (decisionData (List.replicate data.input.length ())) ctor=
      .step next write work input auxiliary index emit) :
    (bank (I:=I) (A:=A) (O:=O) C copies).instruction data
      (configuration (O:=O) C copies (.construct ctor.state) length temporary digits ctor.inputHead 0 digits.length ctor)=
      .step (if emit.isSome then .zeros next ⟨copies,by omega⟩ else .construct next)
        (write,((fun _=>none),none)) work input .stay .stay none := by
  simp only [TapeBank.instruction,decisionData,List.getElem?_nil,Nat.not_lt_zero,ite_false] at table
  simp only [TapeBank.instruction,configuration,bank,Fin.addCases_left,unary_input_map]
  rw [table]

 theorem configuration_constructorStep (copies : ℕ) (data : InputData I A)
    (length temporary digits : List Bool) (ctor : BankConfiguration Unit Q S k)
    (next write work input auxiliary index emit) :
    (bank (I:=I) (A:=A) (O:=O) C copies).advance data
      (configuration (O:=O) C copies (.construct ctor.state) length temporary digits ctor.inputHead 0 digits.length ctor)
      (if emit.isSome then .zeros next ⟨copies,by omega⟩ else .construct next)
      (write,((fun _=>none),none)) work input .stay .stay none=
      configuration (O:=O) C copies (if emit.isSome then .zeros next ⟨copies,by omega⟩ else .construct next)
        length temporary digits
        ((C.advance (decisionData (List.replicate data.input.length ())) ctor next write work input auxiliary index emit).inputHead)
        0 digits.length (C.advance (decisionData (List.replicate data.input.length ())) ctor next write work input auxiliary index emit) := by
  apply BankConfiguration.ext <;> try rfl
  case inputHead => simp [TapeBank.advance,configuration,decisionData]
  case head => simp only [TapeBank.advance,configuration,bank,Fin.addCases_left,BankEmbedding.update_left]
  case tape =>
    simp only [TapeBank.advance,configuration,bank,Fin.addCases_left,BankEmbedding.update_left]
    congr 1
    funext j p
    by_cases same : j=C.select ctor.state
    · subst j
      by_cases position : p=ctor.head (C.select ctor.state)
      · subst p; simp
      · simp [Function.update_of_ne position]
    · simp [Function.update_of_ne same]

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture
