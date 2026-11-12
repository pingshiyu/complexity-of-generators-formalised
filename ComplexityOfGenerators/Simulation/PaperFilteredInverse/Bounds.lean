import ComplexityOfGenerators.Simulation.PaperFilteredInverse.BoundsChecks
import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Execution
import ComplexityOfGenerators.Foundations.ResourceBounds

/-! Concrete space and primitive execution bounds for the filtered inverse.
The supplied tape may be arbitrarily long: only its prescribed prefix is used. -/
namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

def inverseBodyConstant : ℕ :=
  (Source.body M Symbol.inverse (inverseDecode M W) (Source.bank BoundedSource.sourceSlots)).bound

theorem initialStore_bound (seed : PolynomialBound) (n : ℕ) (y w : List α) (bits : BitString)
    (cap : ℕ) (base : n+1≤cap) (input : y.length≤cap) (auxiliary : w.length≤cap)
    (random : seed n≤cap) : StoreBound (initialStore M W seed n y w bits) cap := by
  apply StoreBound.update
  · apply StoreBound.update
    · unfold BoundedSource.preparedMemory
      apply StoreBound.update
      · apply StoreBound.update
        · apply StoreBound.update
          · intro j; simp
          · simpa using (by omega : n≤cap)
        · simpa using base
      · simp only [List.length_map,List.length_take]
        exact (Nat.min_le_left _ _).trans random
    · simpa [letters] using input
  · simpa [letters] using auxiliary

theorem body_initial_bound (seed time q : PolynomialBound) (n : ℕ) (y w : List α) (bits : BitString)
    (cap : ℕ)
    (space : 1+y.length+w.length+n+seed n+3*(time n+1)≤cap)
    (width : q n+1≤cap) :
    StoreBound ((body M W seed time q).eval (initialStore M W seed n y w bits)) (7*cap+1) ∧
    (((body M W seed time q).eval (initialStore M W seed n y w bits)) 25).length≤cap ∧
    (body M W seed time q).cost (initialStore M W seed n y w bits)≤
      (inverseBodyConstant M W+widthBodyConstant M W+3000)*(cap+1)+
        Command.counterBudget seed n+Command.counterBudget time n+Command.counterBudget q n := by
  let s := initialStore M W seed n y w bits
  let a := (firstCall M W seed time).eval s
  let b := (capture M W).eval a
  let data : InputData α α := ⟨y,w,n⟩
  have sBound : StoreBound s cap := initialStore_bound M W seed n y w bits cap
    (by omega) (by omega) (by omega) (by omega)
  have input : (s 11).map (inverseInput M W)=y.map (fun a=>Symbol.inverse (.input a)) := by
    simp [s,initialStore,letters,inverseInput]
  have auxiliary : (s 12).map (inverseAuxiliary M W)=w.map (fun a=>Symbol.inverse (.auxiliary a)) := by
    simp [s,initialStore,letters,inverseAuxiliary]
  have index : (s 13).length=n := by simp [s,initialStore,BoundedSource.preparedMemory]
  have random : s 17=(bits.take (seed n)).map Symbol.bit := by simp [s,initialStore,BoundedSource.preparedMemory]
  have empty : s 14=[] := by simp [s,initialStore,BoundedSource.preparedMemory]
  have bitCode : ∀ bit,inverseBit M W (Symbol.bit bit)=Symbol.inverse (.bit bit) := by intro bit;rfl
  obtain ⟨aBound,aOutput,aCost⟩ := BoundedSource.sourceTrial_bound (O:=α) (Symbol.unit : Cell M W) Symbol.bit M
    Symbol.inverse (inverseDecode M W) (inverseDecode_encode M W) (inverseInput M W)
    (inverseAuxiliary M W) (inverseBit M W) bitCode seed time s data (bits.take (seed n))
    input auxiliary index random empty cap sBound (by dsimp [data];omega) (by dsimp [data];omega)
    (by dsimp [data];omega) space
  change StoreBound a cap at aBound
  change (firstCall M W seed time).cost s≤(inverseBodyConstant M W+200)*(cap+1)+
    Command.counterBudget seed n+Command.counterBudget time n at aCost
  obtain ⟨status,out,state,output,_⟩ := BoundedSource.sourceTrial_result (O:=α) (Symbol.unit : Cell M W) Symbol.bit M
    Symbol.inverse (inverseDecode M W) (inverseDecode_encode M W) (inverseInput M W)
    (inverseAuxiliary M W) (inverseBit M W) bitCode seed time s data (bits.take (seed n))
    input auxiliary index random empty
  change a 0=[Symbol.inverse (.state status)] at state
  change a 10=out.map (fun a=>Symbol.inverse (.output a)) at output
  have aEmpty : a 25=[] := by
    dsimp only [a]
    rw [firstCall_frame M W seed time s 25 (Or.inr (Or.inr (Or.inr rfl)))]
    simp [s,initialStore,BoundedSource.preparedMemory]
  obtain ⟨bBound,bCost⟩ := capture_bound M W a cap aBound (by omega) aEmpty
  have bEq := capture_eval M W a status out state output aEmpty
  have bIndex : (b 13).length=n := by
    simp only [b,bEq,Function.update_of_ne (by decide : (13:Fin 35)≠25),
      Function.update_of_ne (by decide : (13:Fin 35)≠10),Function.update_of_ne (by decide : (13:Fin 35)≠23),
      Function.update_of_ne (by decide : (13:Fin 35)≠33),Function.update_of_ne (by decide : (13:Fin 35)≠26)]
    dsimp only [a]
    rw [firstCall_frame M W seed time s 13 (Or.inr (Or.inr (Or.inl rfl)))]
    exact index
  have bCandidate : b 25=letters M W out.reverse := by simp [b,bEq]
  obtain ⟨cBound,cCost⟩ := checks_bound M W q b n cap bBound bIndex (by omega) width out.reverse bCandidate
  refine ⟨cBound,?_,?_⟩
  · change (((checks M W q).eval b) 25).length≤cap
    rw [checks_candidate_frame]
    exact bBound 25
  · change (firstCall M W seed time).cost s+1+((capture M W).cost a+1+(checks M W q).cost b)≤_
    nlinarith

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
