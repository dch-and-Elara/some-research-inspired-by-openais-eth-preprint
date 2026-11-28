
import J6R23PaddingCensusGeometry

/-! A separate mathematical equivalence-class statement: arbitrary
bijective seated layouts with the same complete diagonal planted pages
have the same *normalized* integer samples. The raw residue and its
factor generally change. No arbitrary table is silently substituted
into the earlier same-seat bit receipt. -/
namespace J6R23PaddingCensus
open scoped BigOperators Polynomial Classical
open P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6RecursiveOrientation J6OrientedSplitSides J6NativeHeightClearing
open J6IntegerLayers J6NativeHeightMesh
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000

variable {S : Type*} [LinearOrder S] [Fintype S] {a b m l : ℕ}

structure LegalRootChart (w : Fin a→S) (hm : m≤b) (hL : 2*l=2^a) where
  seats : Wire w m b l≃Physical a b S
  plant : ∀ (u : Fin m) (j : Fin (2*l)),
    seats (.inl (u,j))=diagonalSlot w (Fin.castLE hm u) (Fin.cast hL j)

def layoutShift (w : Fin a→S) (hm : m≤b) (hL : 2*l=2^a)
    (C : LegalRootChart w hm hL) (t : ℕ) (p : Wire w m b l) : Option (Wire w m b l) :=
  let x := C.seats p
  if e : x.2.val+t<2^a then some (C.seats.symm (x.1,⟨x.2.val+t,e⟩)) else none

theorem chart_shift_iff (w : Fin a→S) (hm : m≤b) (hL : 2*l=2^a)
    (C : LegalRootChart w hm hL) (t : ℕ) (p q : Wire w m b l) :
    layoutShift w hm hL C t p=some q ↔ sameShift t (C.seats p) (C.seats q) := by
  unfold layoutShift
  dsimp only
  by_cases H : (C.seats p).2.val+t<2^a
  · rw [dif_pos H,Option.some.injEq]
    constructor
    · intro h
      have e := congrArg C.seats h
      rw [C.seats.apply_symm_apply] at e
      have e₁ := congrArg (fun z : Physical a b S=>z.1) e
      have e₂ := congrArg (fun z : Physical a b S=>z.2.val) e
      exact ⟨e₁,e₂⟩
    · intro h
      apply C.seats.injective
      rw [C.seats.apply_symm_apply]
      exact Prod.ext h.1 (Fin.ext h.2)
  · rw [dif_neg H]
    constructor
    · simp
    · intro e
      exact (H (e.2 ▸ (C.seats q).2.isLt)).elim

theorem chart_plant_shift (w : Fin a→S) (hm : m≤b) (hL : 2*l=2^a)
    (C : LegalRootChart w hm hL) (t : ℕ) (u : Fin m) (j : Fin (2*l)) :
    layoutShift w hm hL C t (.inl (u,j))=
      if ht : j.val+t<2*l then some (.inl (u,⟨j.val+t,ht⟩)) else none := by
  by_cases H : j.val+t<2*l
  · rw [dif_pos H,chart_shift_iff,C.plant,C.plant]
    exact ⟨rfl,rfl⟩
  · rw [dif_neg H]
    unfold layoutShift
    rw [dif_neg]
    intro e
    apply H
    simpa only [C.plant,diagonalSlot,hL] using e

theorem chart_pad_separate (w : Fin a→S) (hm : m≤b) (hL : 2*l=2^a)
    (C : LegalRootChart w hm hL) (t : ℕ) (p : Pad w m b l×Bool) (u : Fin m) (j : Fin (2*l)) :
    layoutShift w hm hL C t (.inr p)≠some (.inl (u,j)) := by
  intro H
  have e := ((chart_shift_iff w hm hL C t _ _).mp H).1
  let z := C.seats (.inr p)
  let j' := Fin.cast hL.symm z.2
  have page : z.1=(C.seats (.inl (u,j'))).1 := by
    rw [C.plant]
    change (C.seats (.inr p)).1=(diagonalSlot w (Fin.castLE hm u) (Fin.cast hL j')).1
    rw [C.plant] at e
    exact e
  have eq : C.seats (.inr p)=C.seats (.inl (u,j')) := by
    refine Prod.ext page ?_
    rw [C.plant]
    exact Fin.ext rfl
  exact Sum.noConfusion (C.seats.injective eq)

def chartPadShift (w : Fin a→S) (hm : m≤b) (hL : 2*l=2^a)
    (C : LegalRootChart w hm hL) (t : ℕ) (p : Pad w m b l×Bool) :
    Option (Pad w m b l×Bool) :=
  (layoutShift w hm hL C t (.inr p)).bind fun
    | .inl _=>none
    | .inr p=>some p

theorem chart_pad_partial_injective (w : Fin a→S) (hm : m≤b) (hL : 2*l=2^a)
    (C : LegalRootChart w hm hL) (t : ℕ) (p r q : Pad w m b l×Bool)
    (pHit : chartPadShift w hm hL C t p=some q) (rHit : chartPadShift w hm hL C t r=some q) :
    p=r := by
  have actual (x : Pad w m b l×Bool) (h : chartPadShift w hm hL C t x=some q) :
      layoutShift w hm hL C t (.inr x)=some (.inr q) := by
    unfold chartPadShift at h
    cases hz : layoutShift w hm hL C t (.inr x) with
    | none => simp [hz] at h
    | some z =>
      cases z with
      | inl u => simp [hz] at h
      | inr u =>
        have e : u=q := by simpa [hz] using h
        rw [e]
  have hp := (chart_shift_iff w hm hL C t _ _).mp (actual p pHit)
  have hr := (chart_shift_iff w hm hL C t _ _).mp (actual r rHit)
  apply Sum.inr_injective
  apply C.seats.injective
  exact Prod.ext (hp.1.trans hr.1.symm) (Fin.ext (Nat.add_right_cancel (hp.2.trans hr.2.symm)))

theorem chart_read_split (w : Fin a→S) (hm : m≤b) (hL : 2*l=2^a)
    (C : LegalRootChart w hm hL) (t : ℕ) :
    (fun p (x : Wire w m b l→Bool)=>((layoutShift w hm hL C t p).map x).getD false)=
      joinedRead (J6OrientedPlantValue.read t)
        (fun p (x : Pad w m b l×Bool→Bool)=>((chartPadShift w hm hL C t p).map x).getD false) := by
  funext p x
  rcases p with ⟨u,j⟩|⟨d,side⟩
  · rw [chart_plant_shift]
    by_cases hj : j.val+t<2*l <;> simp [joinedRead,J6OrientedPlantValue.read,hj]
  · cases hs : layoutShift w hm hL C t (.inr (d,side)) with
    | none => simp [joinedRead,chartPadShift,hs]
    | some z =>
      rcases z with ⟨u,j⟩|p
      · exact (chart_pad_separate w hm hL C t (d,side) u j hs).elim
      · simp [joinedRead,chartPadShift,hs]

section Mesh
variable {V : Type*} [Fintype V]

noncomputable def chartLoads (m l : ℕ) (w : Fin (J6Mesh.a m)→S)
    (hm : m≤K m) (hL : 2*l=L m)
    (C : LegalRootChart w hm hL) :
    J6Recovery.Addr m→Pad w m (K m) l→ℕ :=
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  fun i=>J6OrientedPadding.count (chartPadShift w hm hL C (index m i))

theorem legal_chart_same_normalized_sample (m l q p : ℕ) (w : Fin (J6Mesh.a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL) (T : Plant V m q)
    (hS : Fintype.card S=64) (hz : coreA T (fun _=>false)=true) (i : J6Recovery.Addr m) :
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    let P := J6SourcePrecision.printed m p
    let n := sampleNum m i
    let d := sampleDen m i
    let read := fun x y=>((layoutShift w hm hL C (index m i) x).map y).getD false
    let z := J6NativeHeightResidue.residueSlot (oldOK T w) (newOK T w) read
      (J6ZeroTransport.reduceBase P (J6NativeHeightDyadic.scalar m i))
    J6IntegerDecode.integerDecode P (J6Recovery.exp m i) (M m) d
      (J6IntegerLayers.factor (P:=Fin m) n d (index m i) q (chartLoads m l w hm hL C i)) z =
      (oldLayer (coreA T) (coreB T) n d,P) := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  have he := (address_index m i).2.2.2
  have ht : index m i≤2*l := by omega
  have hs : index m i+J6Recovery.exp m i=L m := by unfold J6Recovery.exp; omega
  have hP : Fintype.card (Wire w m (K m) l)=M m :=
    J6RepairedCapacity.actual_wire_count m l w hm hL hS
  have hCard : Fintype.card (Wire w m (K m) l)=
      (index m i+J6Recovery.exp m i)*Fintype.card (Fin m)+2*Fintype.card (Pad w m (K m) l) := by
    rw [hs,Fintype.card_fin,←hL,Nat.mul_comm (2*l) m]
    exact wire_cardinality (m:=m) (b:=K m) (l:=l) w
  have hk : ∀ v,chartLoads m l w hm hL C i v≤2 :=
    fun v=>J6OrientedPadding.count_le_two _ (chart_pad_partial_injective w hm hL C (index m i)) v
  dsimp only
  apply J6FactorToInteger.receiver_factorization _ _ _ (coreA T) (coreB T) m p q
    (chartLoads m l w hm hL C) i hk hP hCard
  rw [oldOK_split,newOK_split,chart_read_split,split_rationalSlot,
    J6OrientedPlantValue.planted_factors _ _ _ _ ht,padding_table_factor,J6Recovery.layerSum_factorization]
  have hB : (∑ x : Fin m→Bool, J6OrientedPlantValue.wt (coreB T) x)=(2:ℚ)^q := coreB_count T
  have hA : J6OrientedPlantValue.wt (coreA T) (fun _=>false)=1 := by
    simp [J6OrientedPlantValue.wt,hz]
  have hR : 2*l-index m i=J6Recovery.exp m i := by unfold J6Recovery.exp; rw [hL]
  rw [hB,hA,one_pow,mul_one,←pow_mul,hR]
  unfold J6Recovery.publicFactor chartLoads
  unfold J6OrientedPlantValue.wt oldWeight
  exact (mul_assoc _ _ _).trans (mul_comm _ _)
end Mesh

#print axioms chart_shift_iff
#print axioms chart_plant_shift
#print axioms chart_pad_separate
#print axioms chart_pad_partial_injective
#print axioms chart_read_split
#print axioms legal_chart_same_normalized_sample
end J6R23PaddingCensus
