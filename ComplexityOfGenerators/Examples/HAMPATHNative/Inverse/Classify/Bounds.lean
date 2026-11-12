import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.TailBounds
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Bounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
open Simulation.WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
attribute [local irreducible] routine parse productive parent capacity singleton label
  BaseSearch.bodyBudget Command.counterBudget

def coreBudget (n : ℕ) : ℕ := (n+3)^2
def parentBudget (n : ℕ) : ℕ := 4*(coreBudget n+2)
def labelBudget (n : ℕ) : ℕ := 10*(parentBudget n+1)
def storeBudget (n : ℕ) : ℕ := 1000*(n+2)^2

noncomputable def stackBudget (n : ℕ) : ℕ :=
  10000*(labelBudget n+1)^2+n*(BaseSearch.bodyBudget n+4)+Command.counterBudget BaseSearch.square (n+2)

/-- The classifier is polynomial even on malformed target/label strings.
Only the unary outer index and initial bank size are needed for this bound. -/
theorem routine_bound (s : Store) (n : ℕ) (sizes : StoreBound s (n+1)) (index : (s 34).length = n) :
    StoreBound (routine.eval s) (storeBudget n) ∧ routine.cost s ≤ stackBudget n := by
  let a := parse.eval s
  let b := productive.eval a
  let c := parent.eval b
  let tail : Routine Symbol Symbol 64 := Routine.branch 33 fun word => if word.isNone then singleton else capacity.seq label
  have parsed := parse_bound s (n+1) sizes
  have aSize : StoreBound a (n+2) := by simpa only [Nat.add_assoc] using parsed.1
  have aIndex : (a 34).length = n :=
    (congrArg List.length (parse_frame s 34 (by decide) (by decide) (by decide) (by decide))).trans index
  have productiveResult := productive_bound a (n+2) n aSize aIndex
  have maxBound : max (n+2) (BaseSearch.storeBudget n) ≤ coreBudget n := by
    apply max_le
    · unfold coreBudget; nlinarith
    · unfold BaseSearch.storeBudget encodingLength coreBudget; nlinarith
  have bSize : StoreBound b (coreBudget n) := productiveResult.1.mono maxBound
  have productiveCost : productive.cost a ≤ 200*(coreBudget n+1)+n*(BaseSearch.bodyBudget n+4) := by
    have original := productiveResult.2
    omega
  have parentResult := parent_bound b (coreBudget n) bSize
  have cSize : StoreBound c (parentBudget n) := parentResult.1
  have child : (b 35).length ≤ n+1 := by
    have first : a 35 = List.replicate (headerSize (s 32)) (.bit true) := (parse_values s).1
    have second : b 35 = a 35 := productive_frame a 35 (by decide) (by decide) (by decide)
    rw [second,first,List.length_replicate]
    exact (headerSize_le (s 32)).trans (sizes 32)
  have parentWord : c 37 = List.replicate ((b 35).length+1) (.bit true) := (parent_values b).1
  have widthWord : c 38 = List.replicate (Nat.clog 2 ((b 35).length+1)) (.bit true) := (parent_values b).2
  have parentSize : (c 37).length ≤ n+2 := by rw [parentWord,List.length_replicate]; omega
  have parentPositive : 0 < (c 37).length := by rw [parentWord,List.length_replicate]; omega
  have width : (c 38).length = Nat.clog 2 (c 37).length := by rw [widthWord,parentWord]; simp only [List.length_replicate]
  have power : 2^(c 38).length ≤ parentBudget n := by
    rw [width]
    have upper := RationalSelection.pow_clog_le_twice (c 37).length parentPositive
    unfold parentBudget coreBudget
    nlinarith
  have base : (c 37).length+1 ≤ parentBudget n := by unfold parentBudget coreBudget; nlinarith
  have room : BaseSearch.square (c 37).length+1 ≤ parentBudget n := by
    have squared := Nat.mul_self_le_mul_self (by omega : (c 37).length+1 ≤ n+3)
    simp only [BaseSearch.square,PolynomialBound.eval]
    unfold parentBudget coreBudget
    nlinarith
  have tailResult : StoreBound (tail.eval c) (labelBudget n) ∧
      tail.cost c ≤ 4000*(labelBudget n+1)^2+Command.counterBudget BaseSearch.square (n+2) := by
    by_cases empty : (c 33).head?.isNone = true
    · have checked := singleton_bound c (parentBudget n) (by unfold parentBudget; omega) cSize
      simp only [tail,Routine.branch,empty,ite_true]
      constructor
      · exact checked.1.mono (by unfold labelBudget; omega)
      · have cost := checked.2
        unfold labelBudget
        nlinarith
    · let d := capacity.eval c
      have checked := capacity_bound c (parentBudget n) n cSize base room parentSize
      have dSize : StoreBound d (parentBudget n) := checked.1
      have dWidth : d 38 = c 38 := capacity_frame c 38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have range : 2^(d 38).length ≤ parentBudget n := by rw [dWidth]; exact power
      have decoded := label_bound d (parentBudget n) (by unfold parentBudget; omega) dSize range
      simp only [tail,Routine.branch,empty,Bool.false_eq_true,ite_false]
      constructor
      · exact decoded.1
      · change 1+(capacity.cost c+1+label.cost d) ≤ _
        have first := checked.2
        have second := decoded.2
        unfold labelBudget at *
        nlinarith
  have actual : routine.eval s = tail.eval c := by unfold routine; rfl
  constructor
  · rw [actual]
    apply tailResult.1.mono
    unfold labelBudget parentBudget coreBudget storeBudget
    nlinarith
  · have parseCost : parse.cost s ≤ 600*(n+3)^2 := by simpa only [Nat.add_assoc] using parsed.2
    have parentCost : parent.cost b ≤ 2000*(parentBudget n+1)^2 := parentResult.2
    have tailCost := tailResult.2
    have large : coreBudget n ≤ parentBudget n := by unfold parentBudget; omega
    have larger : parentBudget n+1 ≤ labelBudget n+1 := by unfold labelBudget; omega
    have square := Nat.mul_self_le_mul_self larger
    unfold routine
    change parse.cost s+1+(productive.cost a+1+(parent.cost b+1+tail.cost c)) ≤ _
    unfold stackBudget
    change parse.cost s+1+(productive.cost a+1+(parent.cost b+1+tail.cost c)) ≤
      10000*(labelBudget n+1)^2+n*(BaseSearch.bodyBudget n+4)+Command.counterBudget BaseSearch.square (n+2)
    have core : (n+3)^2 = coreBudget n := rfl
    rw [core] at parseCost
    simp only [← pow_two] at square
    nlinarith

private noncomputable def labelPolynomial : Polynomial ℕ := 10*(4*((Polynomial.X+3)^2+2)+1)

noncomputable def time : PolynomialBound := PolynomialBound.ofPolynomial
  (10000*(labelPolynomial+1)^2+Polynomial.X*(120*((Polynomial.X+1)^2+3)+
    (Command.counterBudget BaseSearch.square).asPolynomial+4)+
      (Command.counterBudget BaseSearch.square).asPolynomial.comp (Polynomial.X+2))

theorem stackBudget_le (n : ℕ) : stackBudget n ≤ time n := by
  unfold time
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one,PolynomialBound.asPolynomial_eval]
  unfold stackBudget labelBudget parentBudget coreBudget BaseSearch.bodyBudget BaseSearch.storeBudget encodingLength labelPolynomial
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  nlinarith

theorem routine_time (s : Store) (n : ℕ) (sizes : StoreBound s (n+1)) (index : (s 34).length = n) :
    routine.cost s ≤ time n := (routine_bound s n sizes index).2.trans (stackBudget_le n)

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
