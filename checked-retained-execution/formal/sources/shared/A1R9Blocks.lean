import AOracleMachineTimeRegister

/-! Bit-serial sparse block lookup and mode counters. The block lookup
charges the actual serialized payload crossed by its tape head. Equality
and counters are computed on bit words; neither is a free Nat operation. -/

namespace A1R9
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open AOracleMachineTimeLocal AOracleMachineTimeZero

def seekBlock {A : Type*} (payload : A → ℕ) (addr : List Bool) :
    List A → Meter (Option A)
  | [] => ⟨none,0⟩
  | a :: as =>
    let n := borrowCore true addr
    let cost := n.steps+2*addr.length+payload a+4
    if n.result.2 then ⟨some a,cost⟩
    else
      let r := seekBlock payload n.result.1 as
      ⟨r.result,r.steps+cost⟩

theorem seekBlock_exact {A : Type*} (payload : A → ℕ) (addr : List Bool) (data : List A) :
    (seekBlock payload addr data).result=data[bitsValue addr]? ∧
      (seekBlock payload addr data).steps≤(10*addr.length+4)*data.length+(data.map payload).sum := by
  induction data generalizing addr with
  | nil => simp [seekBlock]
  | cons a as ih =>
    obtain ⟨hwidth,_,hbit⟩ := borrow_exact true addr
    unfold seekBlock
    dsimp only
    cases hb : (borrowCore true addr).result.2
    · rw [if_neg (by decide : false ≠ true)]
      obtain ⟨hr,hc⟩ := ih (borrowCore true addr).result.1
      rw [hwidth] at hc
      have hd := borrow_decreases addr hb
      constructor
      · rw [hr,← hd,List.getElem?_cons_succ]
      · rw [hbit]
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
        omega
    · rw [if_pos (rfl : true = true)]
      constructor
      · rw [(borrow_zero addr).1 hb]
        rfl
      · rw [hbit]
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
        omega

def eqWord (a b : List Bool) : Meter Bool :=
  let q := orderCore (a.zip b)
  ⟨q.result.2,q.steps⟩

theorem eqWord_exact (a b : List Bool) (h : a.length=b.length) :
    ((eqWord a b).result=true ↔ bitsValue a=bitsValue b) ∧
    (eqWord a b).steps=10*a.length := by
  have he := orderCore_exact (a.zip b)
  simp only [zip_map_fst a b h,zip_map_snd a b h,List.length_zip,← h,min_self] at he
  exact he.2

theorem value_encode_one (p : ℕ) (hp : 0<p) :
    asResidue p (encodeBits p 1)=1 := by
  unfold asResidue
  rw [encodeBits_exact p 1 (one_lt_pow₀ (by decide) hp.ne'),Nat.cast_one]

def negWord (p : ℕ) (a : List Bool) : Meter (List Bool) :=
  let q := addBits (a.map not) (encodeBits p 1)
  ⟨q.result,q.steps+3*p⟩

theorem negWord_exact (p : ℕ) (hp : 0<p) (a : List Bool) (hl : a.length=p) :
    (negWord p a).result.length=p ∧
    asResidue p (negWord p a).result=-asResidue p a ∧
    (negWord p a).steps=15*p := by
  have h₁ : (a.map not).length=p := by simpa using hl
  have h₂ := encodeBits_length p 1
  have hh := addBits_exact (a.map not) (encodeBits p 1) (h₁.trans h₂.symm)
  refine ⟨hh.1.trans h₁,?_,?_⟩
  · change asResidue p (addBits (a.map not) (encodeBits p 1)).result=_
    rw [add_residue p _ _ h₁ h₂,value_encode_one p hp,complement_ring p a hl]
  · change (addBits (a.map not) (encodeBits p 1)).steps+3*p=15*p
    rw [hh.2.2,h₁]
    omega

def countWord (p : ℕ) (key : List Bool) : List (List Bool) → Meter (List Bool)
  | [] => ⟨List.replicate p false,p⟩
  | a::as =>
    let eq := eqWord key a
    let tail := countWord p key as
    let out := if eq.result then addBits tail.result (encodeBits p 1) else Meter.pure tail.result
    ⟨out.result,eq.steps+tail.steps+out.steps+6⟩

theorem countWord_exact (p : ℕ) (key : List Bool) (xs : List (List Bool))
    (hp : 0<p) (fit : xs.length<2^p)
    (widths : ∀ a ∈ xs, a.length=key.length) :
    (countWord p key xs).result.length=p ∧
    bitsValue (countWord p key xs).result =
      xs.countP (fun a => decide (bitsValue key=bitsValue a)) ∧
    (countWord p key xs).steps ≤ p+xs.length*(10*key.length+12*p+6) := by
  induction xs with
  | nil => simp [countWord,value_zero]
  | cons a as ih =>
    have hfit : as.length<2^p := by simp only [List.length_cons] at fit; omega
    obtain ⟨ht,hv,hc⟩ := ih hfit (fun x hx => widths x (List.mem_cons_of_mem _ hx))
    obtain ⟨he,hm⟩ := eqWord_exact key a (widths a List.mem_cons_self).symm
    let tail := countWord p key as
    change tail.result.length=p at ht
    change bitsValue tail.result=as.countP _ at hv
    change tail.steps≤_ at hc
    by_cases h : bitsValue key=bitsValue a
    · have hb := he.2 h
      have hs := addBits_exact tail.result (encodeBits p 1)
        (ht.trans (encodeBits_length p 1).symm)
      have hc' : as.countP (fun u => decide (bitsValue key=bitsValue u))+1<2^p := by
        have hcard : as.countP (fun u => decide (bitsValue key=bitsValue u)) ≤ as.length :=
          List.countP_le_length
        simp only [List.length_cons] at fit
        omega
      have hv' : bitsValue (addBits tail.result (encodeBits p 1)).result =
          as.countP (fun u => decide (bitsValue key=bitsValue u))+1 := by
        rw [hs.2.1,ht,hv,encodeBits_exact p 1 (one_lt_pow₀ (by decide) hp.ne'),
          Nat.mod_eq_of_lt hc']
      refine ⟨?_,?_,?_⟩
      · simpa only [countWord,hb,if_true] using hs.1.trans ht
      · simpa [countWord,hb,tail,h] using hv'
      · simp only [countWord,hb,if_true,List.length_cons]
        change (eqWord key a).steps+tail.steps+(addBits tail.result (encodeBits p 1)).steps+6 ≤
          p+(as.length+1)*(10*key.length+12*p+6)
        rw [hm,hs.2.2,ht,Nat.succ_mul as.length (10*key.length+12*p+6)]
        omega
    · have hb : (eqWord key a).result=false := by
        cases hbool : (eqWord key a).result
        · rfl
        · exact (h (he.1 hbool)).elim
      refine ⟨?_,?_,?_⟩
      · simpa only [countWord,hb,Bool.false_eq_true,if_false,Meter.pure] using ht
      · simpa [countWord,hb,Meter.pure,h] using hv
      · simp only [countWord,hb,Bool.false_eq_true,if_false,Meter.pure,List.length_cons]
        change (eqWord key a).steps+tail.steps+0+6 ≤
          p+(as.length+1)*(10*key.length+12*p+6)
        rw [hm,Nat.succ_mul as.length (10*key.length+12*p+6)]
        omega

#print axioms seekBlock_exact
#print axioms eqWord_exact
#print axioms negWord_exact
#print axioms countWord_exact
end A1R9
