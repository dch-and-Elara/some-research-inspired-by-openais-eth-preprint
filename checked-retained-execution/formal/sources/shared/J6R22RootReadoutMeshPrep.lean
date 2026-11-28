
import J6R22RootReadoutNativeFactor
import J6R22RootReadoutOuterWord

/-! Public odd-mesh word preparation by increment, two additions or
subtractions and two multiplications per grid successor. No lookup of
the large integer numerator/denominator is an executable step. -/
namespace J6R22RootReadout
open scoped BigOperators Polynomial
open A1R10 A1R12 AOracleMachineTime AOracleCoordinates
open J6Mesh J6NativeHeightMesh J9R19CompiledBits
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10500000

structure MeshState (p : ℕ) where
  tick : Word p
  plus : Word p
  minus : Word p

def meshStateFee (p : ℕ) := 5*(32*(p+1)^2)+16*p+18

def meshState {p : ℕ} (hp : 0<p) (base : Word p) : List Unit→Meter (MeshState p)
  | [] => ⟨⟨wordZero p,wordOne p,wordOne p⟩,6*p+10⟩
  | _::rest =>
    let s := meshState hp base rest
    let k := addWord s.result.tick (wordOne p)
    let up := addWord base k.result
    let dn := subWord hp base k.result
    let a := mulWord s.result.plus up.result
    let b := mulWord s.result.minus dn.result
    ⟨⟨k.result,a.result,b.result⟩,s.steps+k.steps+up.steps+dn.steps+a.steps+b.steps+16*p+18⟩

theorem mesh_state_exact {p : ℕ} (hp : 0<p) (base : Word p) (clock : List Unit)
    (L : ℕ) (hbase : wordRead base=(L:ZMod (2^p))) (valid : clock.length≤L) :
    let s := meshState hp base clock
    wordRead s.result.tick=(clock.length:ZMod (2^p)) ∧
    wordRead s.result.plus=(posProd L clock.length:ZMod (2^p)) ∧
    wordRead s.result.minus=(negProd L clock.length:ZMod (2^p)) ∧
    s.steps≤6*p+10+clock.length*meshStateFee p := by
  induction clock with
  | nil =>
    change wordRead (wordZero p)=((0:ℕ):ZMod (2^p)) ∧
      wordRead (wordOne p)=(posProd L 0:ZMod (2^p)) ∧
      wordRead (wordOne p)=(negProd L 0:ZMod (2^p)) ∧
      6*p+10≤6*p+10+0*meshStateFee p
    refine ⟨?_,by simp [wordOne_read p hp,posProd],
      by simp [wordOne_read p hp,negProd],by simp⟩
    simpa only [Nat.cast_zero] using (wordOps p hp).zero_read
  | cons u rest ih =>
    let s := meshState hp base rest
    let k := addWord s.result.tick (wordOne p)
    let up := addWord base k.result
    let dn := subWord hp base k.result
    let A := mulWord s.result.plus up.result
    let B := mulWord s.result.minus dn.result
    have rv : rest.length+1≤L := valid
    obtain ⟨kt,sp,sm,hc⟩ := ih (by omega)
    have sumTick : wordRead k.result = ((rest.length+1:ℕ):ZMod (2^p)) := by
      change wordRead (addWord s.result.tick (wordOne p)).result=_
      rw [addWord_read,wordOne_read p hp]
      change wordRead (meshState hp base rest).result.tick+1=_
      rw [kt,Nat.cast_add,Nat.cast_one]
    refine ⟨sumTick,?_,?_,?_⟩
    · change wordRead A.result=(posProd L (rest.length+1):ZMod (2^p))
      change wordRead (mulWord s.result.plus (addWord base k.result).result).result=_
      rw [mulWord_read,addWord_read,hbase,sumTick]
      change wordRead (meshState hp base rest).result.plus*_=_
      have h : posProd L (rest.length+1) = posProd L rest.length*(L+(rest.length+1)) :=
        Finset.prod_range_succ (fun j=>L+(j+1)) _
      rw [sp,h,Nat.cast_mul]
      simp only [Nat.cast_add,Nat.cast_one]
    · change wordRead B.result=(negProd L (rest.length+1):ZMod (2^p))
      change wordRead (mulWord s.result.minus (subWord hp base k.result).result).result=_
      rw [mulWord_read,subWord_read,hbase,sumTick]
      change wordRead (meshState hp base rest).result.minus*_=_
      have h : negProd L (rest.length+1) = negProd L rest.length*(L-(rest.length+1)) :=
        Finset.prod_range_succ (fun j=>L-(j+1)) _
      rw [sm,h,Nat.cast_mul,Nat.cast_sub rv]
    · have h0 : k.steps≤32*(p+1)^2 := (wordOps p hp).add_cost _ _
      have h1 : up.steps≤32*(p+1)^2 := (wordOps p hp).add_cost _ _
      have h2 : dn.steps≤32*(p+1)^2 := (wordOps p hp).sub_cost _ _
      have h3 : A.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
      have h4 : B.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
      change s.steps+k.steps+up.steps+dn.steps+A.steps+B.steps+16*p+18≤_
      change s.steps≤_ at hc
      simp only [List.length_cons,Nat.add_mul,one_mul]
      unfold meshStateFee at hc ⊢
      omega

def prepareMeshWords {p : ℕ} (hp : 0<p) (m : ℕ) (i : J6Recovery.Addr m) :
    Meter (Word p×Word p) :=
  let pre := meshState hp (dyadicWord p (a m)) (List.replicate (index m i) ())
  let neg := wordSign hp true pre.result.plus
  ⟨(neg.result,pre.result.minus),pre.steps+neg.steps+7*p+12⟩

theorem dyadic_word_read_pow {p : ℕ} (j : ℕ) :
    wordRead (dyadicWord p j)=((2^j:ℕ):ZMod (2^p)) := by
  change ((bitsValue (dyadicBits p j):ℕ):ZMod (2^p))=_
  rw [dyadicBits_value]
  split
  · rfl
  · rename_i h
    have hd : (2:ℕ)^p∣2^j := pow_dvd_pow _ (by omega)
    rw [Nat.cast_zero,eq_comm,ZMod.natCast_eq_zero_iff]
    exact hd

theorem prepare_mesh_exact {p : ℕ} (hp : 0<p) (m : ℕ) (i : J6Recovery.Addr m) :
    let out := prepareMeshWords hp m i
    wordRead out.result.1=(sampleNum m i:ZMod (2^p)) ∧
    wordRead out.result.2=(sampleDen m i:ZMod (2^p)) ∧
    out.steps≤28*p+24+(2*m+1)*meshStateFee p := by
  let s := meshState hp (dyadicWord p (a m)) (List.replicate (index m i) ())
  have H := mesh_state_exact hp (dyadicWord p (a m)) (List.replicate (index m i) ()) (L m)
    (by exact dyadic_word_read_pow _) (by simpa using (address_index m i).2.2.2.le)
  simp only [List.length_replicate] at H
  have neg := wordSign_exact hp true s.result.plus
  have ns := neg.1
  simp only [if_true] at ns
  change wordRead (wordSign hp true s.result.plus).result=(sampleNum m i:ZMod (2^p)) ∧
    wordRead s.result.minus=(sampleDen m i:ZMod (2^p)) ∧
    s.steps+(wordSign hp true s.result.plus).steps+7*p+12≤_
  have pv : wordRead s.result.plus=(posProd (L m) (index m i):ZMod (2^p)) := H.2.1
  refine ⟨?_,by simpa only [sampleDen,Int.cast_natCast] using H.2.2.1,?_⟩
  · rw [ns,pv,sampleNum,Int.cast_neg,Int.cast_natCast]
  · have c := H.2.2.2
    change s.steps≤_ at c
    have c2 := neg.2
    have b := Nat.mul_le_mul_right (meshStateFee p) (address_index m i).2.2.1
    omega

#print axioms mesh_state_exact
#print axioms dyadic_word_read_pow
#print axioms prepare_mesh_exact
end J6R22RootReadout
