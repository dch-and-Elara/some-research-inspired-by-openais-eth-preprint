import A1R12Dyadic

/-! Signed width-bounded source geometry. Grid addresses are traversed
in ordinary integer order, not obtained by querying a factor oracle.
The meter charges the signed-word encoder separately from dyadic
normalization. -/

open scoped BigOperators
namespace A1R12
open A1R10 AOracleMachineTime AOracleMachineTimeTape P1DyadicGrid
open AOracleSuccinctNative P1DyadicGridBridge

def dyadicInt {p : ℕ} (hp : 0<p) (w : ℕ) (u : ℤ) : Meter (ℕ × A1R10.Word p) :=
  let v := dyadicNormalize hp (decide (u<0)) (encodeBits w u.natAbs)
  ⟨v.result,v.steps+8*(w+1)^2+4⟩

def dyadicCap (p w : ℕ) : ℕ := 19*p+14+14*(w+1)^2

theorem encode_signed {w : ℕ} (u : ℤ) (hu : u.natAbs<2^w) :
    signedDenote (decide (u<0)) (encodeBits w u.natAbs)=u := by
  unfold signedDenote
  rw [encodeBits_exact w _ hu]
  by_cases h : u<0
  · simp only [h,decide_true,if_true]
    exact (Int.eq_neg_natAbs_of_nonpos h.le).symm
  · simp only [h,decide_false,Bool.false_eq_true,if_false]
    exact Int.natAbs_of_nonneg (le_of_not_gt h)

theorem dyadicInt_exact {p : ℕ} (hp : 0<p) (w : ℕ) (u : ℤ) (hu : u.natAbs<2^w) :
    (dyadicInt hp w u).result.1=padicValInt 2 u ∧
    wordRead (dyadicInt hp w u).result.2=(oddWord u:ZMod (2^p)) ∧
    (dyadicInt hp w u).steps≤dyadicCap p w := by
  obtain ⟨ha,hb,hc⟩ := dyadicNormalize_exact hp (decide (u<0)) (encodeBits w u.natAbs)
  rw [encode_signed u hu] at ha hb
  rw [encodeBits_length] at hc
  refine ⟨ha,hb,?_⟩
  unfold dyadicInt dyadicCap
  dsimp only
  omega

def gridList (a : ℕ) : List ℤ :=
  (List.range (2^(a+1))).map (fun i : ℕ => (i:ℤ)-pow₂ a)

theorem gridList_length (a : ℕ) : (gridList a).length=2^(a+1) := by simp [gridList]

theorem gridList_nodup (a : ℕ) : (gridList a).Nodup := by
  unfold gridList
  apply (List.nodup_range).map
  intro x y h
  change (x:ℤ)-pow₂ a=(y:ℤ)-pow₂ a at h
  exact_mod_cast (show (x:ℤ)=(y:ℤ) by omega)

theorem gridList_mem (a : ℕ) (t : ℤ) : t ∈ gridList a ↔ t∈grid a := by
  have hpow : ((2:ℕ)^(a+1):ℤ)=2*pow₂ a := by simp [pow₂,pow_succ,mul_comm]
  rw [gridList,List.mem_map,mem_grid]
  constructor
  · rintro ⟨j,hj,rfl⟩
    have hi : (j:ℤ)<((2:ℕ)^(a+1):ℤ) := by exact_mod_cast (List.mem_range.mp hj)
    rw [hpow] at hi
    have hj0 : (0:ℤ)≤j := Int.natCast_nonneg _
    omega
  · intro ht
    let j := (t+pow₂ a).toNat
    have hv : (j:ℤ)=t+pow₂ a := Int.toNat_of_nonneg (by omega)
    refine ⟨j,List.mem_range.mpr ?_,by omega⟩
    have h : (j:ℤ)<((2:ℕ)^(a+1):ℤ) := by rw [hv,hpow]; omega
    exact_mod_cast h

theorem gridList_toFinset (a : ℕ) : (gridList a).toFinset=grid a := by
  ext t
  rw [List.mem_toFinset,gridList_mem]

/-- The true signed grid difference fits in a+1 magnitude bits, even
at the two ends. No valuation bound is used to truncate this word. -/
theorem diff_width {a : ℕ} {t k : ℤ} (ht : t∈grid a) (hk : k∈grid a) :
    (t-k).natAbs < 2^(a+1) := by
  rw [mem_grid] at ht hk
  have hpow : ((2:ℕ)^(a+1):ℤ)=2*pow₂ a := by simp [pow₂,pow_succ,mul_comm]
  have h : ((t-k).natAbs:ℤ)<((2:ℕ)^(a+1):ℤ) := by
    rw [hpow]
    by_cases h : 0≤t-k
    · rw [Int.natAbs_of_nonneg h]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (le_of_lt (lt_of_not_ge h))]
      omega
  exact_mod_cast h

/-- A single conservative width covers every mode/row, even ineligible
targets where the crossing distance can be zero or have larger level. -/
theorem cross_width {a i : ℕ} {t : ℤ} (ht : t∈grid a)
    {x u : ℕ} (hx : x<2^a) (hu : u<2^(i+1)) :
    (crossingInt t x u).natAbs < 2^(a+i+2) := by
  rw [mem_grid] at ht
  have hA : ((2:ℕ)^a:ℤ)=pow₂ a := by simp [pow₂]
  have hB : ((2:ℕ)^(a+i+2):ℤ)=2*((2:ℕ)^(a+i+1):ℤ) := by simp [pow_succ,mul_comm]
  have h1 : pow₂ a≤((2:ℕ)^(a+i+1):ℤ) := by
    rw [← hA]
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) (by omega : a≤a+i+1))
  have h2 : ((2:ℕ)^(i+1):ℤ)≤((2:ℕ)^(a+i+1):ℤ) := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) (by omega : i+1≤a+i+1))
  have h3 : (x:ℤ)<pow₂ a := by rw [← hA]; exact_mod_cast hx
  have h4 : (u:ℤ)<((2:ℕ)^(i+1):ℤ) := by exact_mod_cast hu
  have h : ((crossingInt t x u).natAbs:ℤ)<((2:ℕ)^(a+i+2):ℤ) := by
    rw [hB]
    unfold crossingInt
    by_cases h : 0≤t-(u:ℤ)+x
    · rw [Int.natAbs_of_nonneg h]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (le_of_lt (lt_of_not_ge h))]
      omega
  exact_mod_cast h

#print axioms dyadicInt_exact
#print axioms gridList_toFinset
#print axioms diff_width
#print axioms cross_width
end A1R12


