import J6R15ModeCostCursor

/-! Paid counters from an input bound word. The well-founded index is
a proof of termination, not an integer budget consulted by the loop.
Each step does a full fixed-width comparison and a ripple increment. -/
namespace J6R17ModeTape
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits J6R15ModeCost

def wordLT {q : ℕ} (x y : Word q) : Meter Bool :=
  compareBits x.bits y.bits

theorem wordLT_exact {q : ℕ} (x y : Word q) :
    ((wordLT x y).result=true ↔ x.val<y.val) ∧ (wordLT x y).steps=10*q := by
  obtain ⟨h,c⟩ := compareBits_exact x.bits y.bits (x.size.trans y.size.symm)
  refine ⟨h,?_⟩
  simpa only [wordLT,x.size] using c

theorem incrFits {q : ℕ} {lo hi : Word q} (h : (wordLT lo hi).result=true) :
    lo.val+1<2^q := by
  have h₁ := (wordLT_exact lo hi).1.mp h
  have h₂ := val_lt hi
  omega

def checkedBump {q : ℕ} (hq : 0<q) (hi lo : Word q)
    (h : (wordLT lo hi).result=true) : Meter {w : Word q // w.val=lo.val+1} :=
  let k := increment lo
  ⟨⟨k.result,(increment_exact hq lo (incrFits h)).1⟩,k.steps⟩

def wordLoop {q : ℕ} (hq : 0<q) (hi lo : Word q) : Meter (List (Word q)) :=
  let c := wordLT lo hi
  if h : c.result=true then
    let k := checkedBump hq hi lo h
    let t := wordLoop hq hi k.result.val
    ⟨lo::t.result,c.steps+k.steps+t.steps+4*q+12⟩
  else ⟨[],c.steps+4⟩
termination_by hi.val-lo.val
decreasing_by
  have hv := k.result.property
  have hh : (wordLT lo hi).result=true := by assumption
  have ht := (wordLT_exact lo hi).1.mp hh
  change hi.val-(k.result.val).val<hi.val-lo.val
  rw [hv]
  omega

theorem wordLoop_exact {q : ℕ} (hq : 0<q) (hi lo : Word q) :
    let t := wordLoop hq hi lo
    t.result=(List.range' lo.val (hi.val-lo.val)).map word ∧
    t.steps=(hi.val-lo.val)*(27*q+16)+10*q+4 := by
  rw [wordLoop]
  dsimp only
  by_cases h : lo.val<hi.val
  · have hb := (wordLT_exact lo hi).1.mpr h
    rw [dif_pos hb]
    dsimp only [checkedBump]
    let k := increment lo
    obtain ⟨hv,hc⟩ := increment_exact hq lo (incrFits hb)
    obtain ⟨hr,ht⟩ := wordLoop_exact hq hi k.result
    have hh : hi.val-lo.val=(hi.val-k.result.val)+1 := by
      change k.result.val=_ at hv
      omega
    have hV : k.result.val=lo.val+1 := hv
    refine ⟨?_,?_⟩
    · change lo::(wordLoop hq hi k.result).result=_
      rw [hr,hh,List.range'_succ,List.map_cons,valued_word,hV]
    · change (wordLT lo hi).steps+k.steps+(wordLoop hq hi k.result).steps+4*q+12=_
      rw [(wordLT_exact lo hi).2,hc,ht,hh]
      simp only [Nat.add_mul,one_mul]
      ring
  · have hb : ¬ (wordLT lo hi).result=true := fun e => h ((wordLT_exact lo hi).1.mp e)
    rw [dif_neg hb]
    have hD : hi.val-lo.val=0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
    rw [hD]
    simpa only [List.range'_zero,List.map_nil,zero_mul,zero_add,true_and] using
      congrArg (·+4) (wordLT_exact lo hi).2
termination_by hi.val-lo.val
decreasing_by
  change hi.val-(increment lo).result.val<hi.val-lo.val
  change (increment lo).result.val=lo.val+1 at hv
  omega

def wordSpan {q : ℕ} (hq : 0<q) (hi : Word q) : Meter (List (Word q)) :=
  let z := wordLoop hq hi (word 0)
  ⟨z.result,z.steps+2*q+6⟩

def spanFee (q n : ℕ) : ℕ := n*(27*q+16)+12*q+10

theorem wordSpan_exact {q : ℕ} (hq : 0<q) (hi : Word q) :
    let z := wordSpan hq hi
    z.result=(List.range' 0 hi.val).map word ∧ z.steps=spanFee q hi.val := by
  obtain ⟨he,hc⟩ := wordLoop_exact hq hi (word 0)
  have h := word_val (q:=q) (Nat.two_pow_pos q)
  simp only [h,Nat.sub_zero] at he hc
  dsimp only [wordSpan]
  rw [he,hc,spanFee]
  constructor
  · rfl
  · omega

/-- Use the same precision word as the exponent stream. Dropping the
zero counter leaves the positive weights (encoding Taylor order b as
weight b+1) rather than assuming an externally supplied weight table. -/
def positiveSpan {q : ℕ} (hq : 0<q) (p : Word q) : Meter (List (Word q)) :=
  let z := wordSpan hq p
  ⟨z.result.drop 1,z.steps+4⟩

theorem positiveSpan_exact {q : ℕ} (hq : 0<q) (p : Word q) (hp : 0<p.val) :
    let z := positiveSpan hq p
    z.result=(List.range' 1 (p.val-1)).map word ∧ z.steps=spanFee q p.val+4 := by
  have h : p.val=(p.val-1)+1 := by omega
  obtain ⟨he,hc⟩ := wordSpan_exact hq p
  dsimp only [positiveSpan]
  rw [he,hc]
  refine ⟨?_,rfl⟩
  conv_lhs => rw [h]
  rw [List.range'_succ,List.map_cons,List.drop_succ_cons,List.drop_zero]

/-- The machine writing the upper bound on residue tiles uses a
single hot bit. The unary coordinate is consumed one level at a time;
no exponentiation routine or decoded power table is used. -/
def tileBits : ℕ → ℕ → List Bool
  | 0,_=>[]
  | q+1,0=>true::List.replicate q false
  | q+1,i+1=>false::tileBits q i

theorem tileBits_size (q i : ℕ) : (tileBits q i).length=q := by
  induction q generalizing i with
  | zero => rfl
  | succ q ih => cases i <;> simp [tileBits,ih]

private theorem zero_bits (q : ℕ) : bitsValue (List.replicate q false)=0 := by
  induction q with
  | zero => rfl
  | succ q ih => simp [List.replicate_succ,bitsValue,ih]

theorem tileBits_value (q i : ℕ) (h : i<q) : bitsValue (tileBits q i)=2^i := by
  induction q generalizing i with
  | zero => omega
  | succ q ih =>
    cases i with
    | zero => simp [tileBits,bitsValue,zero_bits]
    | succ i =>
      have hi : i<q := by omega
      simp [tileBits,bitsValue,ih i hi,pow_succ,Nat.mul_comm]

def tileBound (q i : ℕ) : Meter (Word q) :=
  ⟨⟨tileBits q (i+1),tileBits_size q (i+1)⟩,4*q+8⟩

theorem tileBound_exact (q i : ℕ) (h : i+1<q) :
    (tileBound q i).result.val=2^(i+1) ∧ (tileBound q i).steps=4*q+8 :=
  ⟨tileBits_value q _ h,rfl⟩

#print axioms wordLT_exact
#print axioms wordLoop_exact
#print axioms wordSpan_exact
#print axioms positiveSpan_exact
#print axioms tileBound_exact
end J6R17ModeTape



