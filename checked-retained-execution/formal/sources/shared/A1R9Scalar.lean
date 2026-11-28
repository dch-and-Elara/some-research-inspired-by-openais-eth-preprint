import A1R9Row

/-! Exact metered multiplication of the selected scalar row factors.
Selections are performed by scanning their encoded record, rather than
being granted as a free witness-dependent oracle. -/

namespace A1R9
open scoped BigOperators
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open AOracleMachineTimeLocal AOracleMachineTimeZero AOracleSuccinct AOracleWitness

theorem sum_map_le_length {A : Type*} (l : List A) (f : A → ℕ) (q : ℕ)
    (h : ∀ a∈l, f a≤q) : (l.map f).sum≤l.length*q := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

def zeroAnswer (p : ℕ) : Meter (Bool × List Bool) :=
  ⟨(false,List.replicate p false),p⟩

def selectPick (p : ℕ) (x : List Bool) (y : Bool) (addr : List Bool)
    (t : List PickTape) : Meter (Bool × List Bool) :=
  let q := seekBlock pickPayload addr t
  let a := q.result.elim (zeroAnswer p) (runPick p x y)
  ⟨a.result,q.steps+a.steps+3⟩

def selectBudget (m b c bc p s : ℕ) : ℕ :=
  (m+1)*(10*b+4+(s*(bc+p+2)+p+3)) + pickedBudget c bc p s+3

theorem selectPick_exact {r c m delta p : ℕ} (b bc s : ℕ)
    (hp : 0<p) (hmode : m+1≤2^b) (hcol : c≤2^bc)
    (L : Recipes (ZMod (2^p)) r c m delta) (w : Witness r c m) (j : Fin r)
    (hL : ∀ j, (L.localRecipe j).length≤s) (hM : ∀ k, (L.moment k).length≤s) :
    let u := selectPick p (List.ofFn w.2.1) (w.1 j) (encodeBits b (w.2.2 j).val) (pickTape bc L j)
    u.result.1=allowed (rootTerms L) w.2.2 j ∧
    u.result.2.length=p ∧ asResidue p u.result.2=evaluateRow L w j ∧
    u.steps≤selectBudget m b c bc p s := by
  let slot := w.2.2 j
  let h := seekBlock pickPayload (encodeBits b slot.val) (pickTape bc L j)
  obtain ⟨he,ht⟩ := seekBlock_exact pickPayload (encodeBits b slot.val) (pickTape bc L j)
  have hget : h.result=some (pickAt bc L j slot) := by
    change h.result=_ at he
    rw [he,encodeBits_exact b slot.val (slot.isLt.trans_le hmode)]
    unfold pickTape
    rw [List.getElem?_ofFn]
    simp [slot.isLt]
  have hlen : (pickTape bc L j).length=m+1 := List.length_ofFn
  have hbytes := sum_map_le_length (pickTape bc L j) pickPayload (s*(bc+p+2)+p+3) (by
    intro q hq
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hq
    exact pickAt_payload bc s L j a hL hM)
  rw [hlen] at hbytes
  rw [encodeBits_length,hlen] at ht
  obtain ⟨hr,hl,hv,hc⟩ := runPick_at bc s hp hcol L w j hL hM
  change (runPick p (List.ofFn w.2.1) (w.1 j) (pickAt bc L j slot)).steps≤_ at hc
  unfold selectPick
  dsimp only
  change _ ∧ _ ∧ _ ∧ h.steps+
    (h.result.elim (zeroAnswer p) (runPick p (List.ofFn w.2.1) (w.1 j))).steps+3≤_
  -- Rewrite the same computed block in both its value and cost.
  change h.steps≤_ at ht
  have hcost : h.steps +
      (runPick p (List.ofFn w.2.1) (w.1 j) (pickAt bc L j slot)).steps+3 ≤
      selectBudget m b c bc p s := by
    unfold selectBudget
    rw [Nat.mul_add (m+1) (10*b+4) (s*(bc+p+2)+p+3),Nat.mul_comm (m+1) (10*b+4)]
    omega
  simpa only [show (seekBlock pickPayload (encodeBits b (w.2.2 j).val) (pickTape bc L j)) = h
    from rfl, hget,Option.elim_some] using ⟨hr,hl,hv,hcost⟩

def runSelected (p : ℕ) (x : List Bool) :
    List Bool → List (List Bool) → List (List PickTape) → Meter (Bool × List Bool)
  | [],[],[] => ⟨(true,encodeBits p 1),p⟩
  | y::ys,a::as,t::ts =>
    let hd := selectPick p x y a t
    let tl := runSelected p x ys as ts
    let u := multiply hd.result.2 tl.result.2
    ⟨(hd.result.1 && tl.result.1,u.result),hd.steps+tl.steps+u.steps+6⟩
  | _,_,_ => zeroAnswer p

def guessedAllocation {r c m : ℕ} (b : ℕ) (w : Witness r c m) : List (List Bool) :=
  List.ofFn fun j => encodeBits b (w.2.2 j).val

def rowStageBudget (m b c bc p s : ℕ) : ℕ :=
  selectBudget m b c bc p s+16*(p+1)^2+6

theorem runSelected_list {r c m delta p : ℕ} (b bc s : ℕ)
    (hp : 0<p) (hmode : m+1≤2^b) (hcol : c≤2^bc)
    (L : Recipes (ZMod (2^p)) r c m delta) (w : Witness r c m)
    (hL : ∀ j, (L.localRecipe j).length≤s) (hM : ∀ k, (L.moment k).length≤s)
    (rows : List (Fin r)) :
    let u := runSelected p (List.ofFn w.2.1) (rows.map w.1)
      (rows.map fun j => encodeBits b (w.2.2 j).val) (rows.map (pickTape bc L))
    (u.result.1=true ↔ ∀ j∈rows, allowed (rootTerms L) w.2.2 j=true) ∧
    u.result.2.length=p ∧
    asResidue p u.result.2=(rows.map (evaluateRow L w)).prod ∧
    u.steps≤p+rows.length*rowStageBudget m b c bc p s := by
  induction rows with
  | nil => simp [runSelected,encodeBits_length,value_encode_one p hp]
  | cons j js ih =>
    let u := selectPick p (List.ofFn w.2.1) (w.1 j)
      (encodeBits b (w.2.2 j).val) (pickTape bc L j)
    let v := runSelected p (List.ofFn w.2.1) (js.map w.1)
      (js.map fun j => encodeBits b (w.2.2 j).val) (js.map (pickTape bc L))
    obtain ⟨he,hlen,hs,hcost⟩ := selectPick_exact b bc s hp hmode hcol L w j hL hM
    obtain ⟨hp',hl',hv',hc'⟩ := ih
    change u.result.1=_ at he
    change u.result.2.length=p at hlen
    change asResidue p u.result.2=_ at hs
    change u.steps≤_ at hcost
    change (v.result.1=true ↔ _) at hp'
    change v.result.2.length=p at hl'
    change asResidue p v.result.2=_ at hv'
    change v.steps≤_ at hc'
    let q := multiply u.result.2 v.result.2
    obtain ⟨ql,qv,_⟩ := multiply_result p u.result.2 v.result.2 hlen
    have qc := square_word_cost p u.result.2 v.result.2 hlen hl'
    change ((u.result.1 && v.result.1) = true ↔ ∀ i∈j::js, _) ∧
      q.result.length=p ∧ asResidue p q.result=(List.map (evaluateRow L w) (j::js)).prod ∧
      u.steps+v.steps+q.steps+6≤p+(js.length+1)*rowStageBudget m b c bc p s
    refine ⟨?_,ql,?_,?_⟩
    · simp [he,hp']
    · rw [qv,hs,hv',List.map_cons,List.prod_cons]
    · change q.steps≤_ at qc
      rw [Nat.succ_mul js.length (rowStageBudget m b c bc p s)]
      unfold rowStageBudget at hc' ⊢
      omega

def runAllRows {r c m delta p : ℕ} (b bc : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) (w : Witness r c m) : Meter (Bool × List Bool) :=
  runSelected p (List.ofFn w.2.1) (List.ofFn w.1)
    (guessedAllocation b w) (List.ofFn (pickTape bc L))

theorem runAllRows_exact {r c m delta p : ℕ} (b bc s : ℕ)
    (hp : 0<p) (hmode : m+1≤2^b) (hcol : c≤2^bc)
    (L : Recipes (ZMod (2^p)) r c m delta) (w : Witness r c m)
    (hL : ∀ j, (L.localRecipe j).length≤s) (hM : ∀ k, (L.moment k).length≤s) :
    let u := runAllRows b bc L w
    (u.result.1=true ↔ legal (rootTerms L) w.2.2) ∧ u.result.2.length=p ∧
      asResidue p u.result.2=(∏ j : Fin r,evaluateRow L w j) ∧
      u.steps≤p+r*rowStageBudget m b c bc p s := by
  have h := runSelected_list b bc s hp hmode hcol L w hL hM (List.finRange r)
  simpa [List.finRange,guessedAllocation,runAllRows,legal,List.map_ofFn,List.prod_ofFn,Function.comp_def]
    using h

#print axioms selectPick_exact
#print axioms runSelected_list
#print axioms runAllRows_exact
end A1R9
