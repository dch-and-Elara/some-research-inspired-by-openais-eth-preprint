
import J6R15SignedReadNative
import J9R19CompiledBitsLocal

/-! Public root shape and height on the same signed fallback, not a
promised factorization for an unrelated supplied tensor. -/
namespace J6R22RootReadout
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6RepairedCentered J6NativeHeightMesh J6R15SignedRead
open J9R19CompiledBits J6IntegerLayers
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000

def outerMeshWidth (m : ℕ) : ℕ := (2*m+1)*(a m+1)

theorem source_mesh_fits (m : ℕ) (i : J6Recovery.Addr m) :
    Fits (outerMeshWidth m) (sampleNum m i) ∧ Fits (outerMeshWidth m) (sampleDen m i) := by
  have le := Nat.mul_le_mul_right (a m+1) (address_index m i).2.2.1
  have H : (2:ℕ)^(index m i*(a m+1)) ≤ 2^(outerMeshWidth m) :=
    Nat.pow_le_pow_right (by decide) le
  obtain ⟨_,hn,hd⟩ := mesh_bounds m i
  constructor
  · apply Nat.le_trans _ H
    exact_mod_cast (by simpa using hn : ((sampleNum m i).natAbs:ℤ) ≤ ((2:ℕ)^(index m i*(a m+1)):ℤ))
  · apply Nat.le_trans _ H
    exact_mod_cast (by simpa using hd : ((sampleDen m i).natAbs:ℤ) ≤ ((2:ℕ)^(index m i*(a m+1)):ℤ))

theorem source_mesh_injective (m : ℕ) :
    Function.Injective (fun i : J6Recovery.Addr m => (sampleNum m i:ℚ)/sampleDen m i) := by
  intro i j h
  apply (negative_distinct_points m).2
  simpa only [mesh_fraction] using h

theorem centered_root_bound (p e : ℕ) (odd : Odd e) (D X : ℤ)
    (positive : 0<D) (h : 2*|D*X^e| < (↑((2:ℕ)^p):ℤ)) :
    X.natAbs<2^p := by
  have eP : 0<e := by obtain ⟨j,hj⟩ := odd; omega
  have bound : (D*X^e).natAbs<2^p := by
    have a1 : |D*X^e| < (↑((2:ℕ)^p):ℤ) := by
      have h0 := abs_nonneg (D*X^e)
      omega
    exact_mod_cast (by simpa using a1 : ((D*X^e).natAbs:ℤ)<(↑((2:ℕ)^p):ℤ))
  rw [Int.natAbs_mul,Int.natAbs_pow] at bound
  have hD := Int.natAbs_pos.mpr positive.ne'
  have g : X.natAbs≤X.natAbs^e := by
    obtain ⟨e',rfl⟩ := Nat.exists_eq_succ_of_ne_zero eP.ne'
    by_cases hz : X.natAbs=0
    · simp [hz]
    · rw [pow_succ,mul_comm]
      exact Nat.le_mul_of_pos_right _ (pow_pos (Nat.pos_of_ne_zero hz) _)
  exact (g.trans (Nat.le_mul_of_pos_left _ hD)).trans_lt bound

variable {W S : Type*} [LinearOrder S] [Fintype S] [Fintype W]

noncomputable def rootPublicFactor (m q l : ℕ)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m) : ℤ :=
  factor (P:=Fin m) (sampleNum m i) (sampleDen m i) (index m i) q
    (J6PhysicalInteger.loads m l mask w hm hL i)

noncomputable def rootOldNumerator (m q : ℕ) (T : Plant W m q) (i : J6Recovery.Addr m) : ℤ :=
  oldLayer (coreA T) (coreB T) (sampleNum m i) (sampleDen m i)

theorem root_public_factor_pos (m q l : ℕ)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m) :
    0<rootPublicFactor m q l mask w hm hL i := by
  apply public_pos _ _ _ _ _ (mesh_bounds m i).1
  unfold sampleNum
  exact neg_nonpos.mpr (Int.natCast_nonneg _)

theorem source_padding_load_le_two (m l : ℕ)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m) :
    ∀ v, J6PhysicalInteger.loads m l mask w hm hL i v ≤ 2 := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  intro v
  unfold J6PhysicalInteger.loads
  apply J6OrientedPadding.count_le_two
  intro p r q hp hr
  exact Sum.inr_injective
    (J6OrientedShift.successor_injective mask w hm hL (index m i) _ _ _
      (padShift_apply mask w hm hL (index m i) p q hp)
      (padShift_apply mask w hm hL (index m i) r q hr))

theorem source_actual_factor (m q l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m)
    (hz : coreA T (fun _=>false)=true) :
    physicalCleared m q l T mask w hm hL i =
      rootPublicFactor m q l mask w hm hL i*(rootOldNumerator m q T i)^J6Recovery.exp m i := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  have hCard : Fintype.card (Ports m l w) =
      (index m i+J6Recovery.exp m i)*Fintype.card (Fin m)+2*Fintype.card (Pad w m (K m) l) := by
    have he := (address_index m i).2.2.2
    have sh : index m i+J6Recovery.exp m i=L m := by unfold J6Recovery.exp; omega
    rw [sh,Fintype.card_fin,←hL,Nat.mul_comm (2*l) m]
    exact wire_cardinality (m:=m) (b:=K m) (l:=l) w
  exact J6FactorToInteger.clear_factorization _ _ _ (coreA T) (coreB T)
    m q (J6PhysicalInteger.loads m l mask w hm hL) i
    (source_padding_load_le_two m l mask w hm hL i) hCard
    (J6PhysicalInteger.physical_layer_eq m l q mask w hm hL T hz i)

theorem source_odd_root_fits (m q b l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m)
    (hS : Fintype.card S=64) (hz : coreA T (fun _=>false)=true) :
    (rootOldNumerator m q T i).natAbs<2^J6SourcePrecision.printed m b := by
  apply centered_root_bound _ _ (J6Recovery.odd_exp m i)
    (rootPublicFactor m q l mask w hm hL i) _ (root_public_factor_pos m q l mask w hm hL i)
  rw [← source_actual_factor m q l T mask w hm hL i hz]
  exact physicalCleared_fits m q b l T mask w hm hL i hS

#print axioms source_mesh_fits
#print axioms source_mesh_injective
#print axioms centered_root_bound
#print axioms root_public_factor_pos
#print axioms source_padding_load_le_two
#print axioms source_actual_factor
#print axioms source_odd_root_fits
end J6R22RootReadout
