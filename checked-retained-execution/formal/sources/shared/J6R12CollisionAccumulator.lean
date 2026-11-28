import J6R12CollisionBits

/-!
# Fixed-width accumulation of the ordered edge-pair contributions

The numerical interpretation never appears in the program. A checked
total bound prevents modular wraparound in every intermediate
accumulation. The remaining word-copy and control budget per term is
made explicit, separately from any graph or marginal-table I/O.
-/

namespace J6R12CollisionAccumulator
open scoped BigOperators Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits J6R11CollisionCost

def tally {T : Type*} (w : ℕ) (term : T → Meter (List Bool)) :
    List T → Meter (List Bool)
  | [] => ⟨List.replicate w false,w⟩
  | t::ts =>
    let q := term t
    let s := tally w term ts
    let a := addBits q.result s.result
    ⟨a.result,q.steps+s.steps+a.steps+2*w+8⟩

theorem zero_value (w : ℕ) : bitsValue (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ,bitsValue,ih]

theorem tally_exact {T : Type*} (w g : ℕ) (term : T → Meter (List Bool)) (f : T → ℕ)
    (xs : List T)
    (ht : ∀ t ∈ xs, (term t).result.length=w ∧ bitsValue (term t).result=f t ∧
      (term t).steps≤g)
    (hfit : (xs.map f).sum<2^w) :
    let a := tally w term xs
    a.result.length=w ∧ bitsValue a.result=(xs.map f).sum ∧
      a.steps≤w+(g+14*w+8)*xs.length := by
  induction xs with
  | nil => simp [tally,zero_value]
  | cons t ts ih =>
    obtain ⟨htl,htv,hts⟩ := ht t List.mem_cons_self
    have fit' : (ts.map f).sum<2^w := by simp only [List.map_cons,List.sum_cons] at hfit; omega
    obtain ⟨hsl,hsv,hss⟩ := ih (fun u hu => ht u (List.mem_cons_of_mem _ hu)) fit'
    let q := term t
    let s := tally w term ts
    have ha := addBits_exact q.result s.result (htl.trans hsl.symm)
    change (addBits q.result s.result).result.length=w ∧
      bitsValue (addBits q.result s.result).result=(f t+(ts.map f).sum) ∧
      q.steps+s.steps+(addBits q.result s.result).steps+2*w+8≤
        w+(g+14*w+8)*(ts.length+1)
    refine ⟨ha.1.trans htl,?_,?_⟩
    · rw [ha.2.1,htl,htv,hsv,Nat.mod_eq_of_lt]
      exact hfit
    · rw [ha.2.2,htl,Nat.mul_succ]
      change q.steps≤g at hts
      change s.steps≤w+(g+14*w+8)*ts.length at hss
      omega

def scoreTape (w kR kC b : ℕ) (L : Literals) (ts : List PairTape) : Meter (List Bool) :=
  tally w (pairBits kR kC b w L) ts

noncomputable section

/-- The stored values are exactly the J6 integer score, not just
congruent modulo 2^w. The witness list indexes edge pairs, including
ordered repeated endpoints and diagonal pairs. -/
theorem scoreTape_exact {E R C A : Type*} [Fintype E] [Fintype A] [Nonempty A]
    (w kR kC b : ℕ) (rCode : R → ℕ) (cCode : C → ℕ) (aCode : A → ℕ)
    (hr : Function.Injective rCode) (hc : Function.Injective cCode) (ha : Function.Injective aCode)
    (hR : ∀ i, rCode i<2^kR) (hC : ∀ i, cCode i<2^kC) (hA : ∀ i, aCode i<2^b)
    (h₁ : 1<2^w) (hB : Fintype.card A<2^w) (hBB : (Fintype.card A)^2<2^w)
    (row : E → R) (col : E → C) (p : R⊕C → Option A)
    (pairs : List (E×E)) (hn : pairs.Nodup) (hAll : ∀ ef : E×E, ef ∈ pairs)
    (hfit : integerScore row col p<2^w) :
    let s := scoreTape w kR kC b (makeLiterals w (Fintype.card A))
      (pairs.map (packPair kR kC b rCode cCode aCode row col p))
    s.result.length=w ∧ bitsValue s.result=integerScore row col p ∧
      s.steps≤w+(pairBudget kR kC b w+14*w+8)*(Fintype.card E)^2 := by
  let pack := packPair kR kC b rCode cCode aCode row col p
  let t := pairBits kR kC b w (makeLiterals w (Fintype.card A))
  let f := contribution row col p
  have hset : pairs.toFinset = Finset.univ := by
    ext ef
    simp [hAll ef]
  have hlen : pairs.length=(Fintype.card E)^2 := by
    rw [← List.toFinset_card_of_nodup hn,hset,Finset.card_univ,Fintype.card_prod,pow_two]
  have hs : (pairs.map f).sum=integerScore row col p := by
    rw [← List.sum_toFinset _ hn, hset]
    rfl
  have map_tally : tally w t (pairs.map pack) = tally w (fun e => t (pack e)) pairs := by
    clear hlen hs hset hfit hn hAll
    induction pairs with
    | nil => rfl
    | cons ef es ih => simp only [List.map_cons,tally,ih]
  have hh (e : E×E) (_ : e ∈ pairs) :
      (t (pack e)).result.length=w ∧ bitsValue (t (pack e)).result=f e ∧
        (t (pack e)).steps≤pairBudget kR kC b w :=
    packed_pair_exact kR kC b w rCode cCode aCode hr hc ha hR hC hA h₁ hB hBB row col p e
  change (tally w t (pairs.map pack)).result.length=w ∧
    bitsValue (tally w t (pairs.map pack)).result=integerScore row col p ∧
    (tally w t (pairs.map pack)).steps≤w+(pairBudget kR kC b w+14*w+8)*(Fintype.card E)^2
  rw [map_tally]
  have q := tally_exact w (pairBudget kR kC b w) (fun e => t (pack e)) f pairs hh
    (hs ▸ hfit)
  rw [hs,hlen] at q
  exact q

#print axioms tally_exact
#print axioms scoreTape_exact

end
end J6R12CollisionAccumulator
