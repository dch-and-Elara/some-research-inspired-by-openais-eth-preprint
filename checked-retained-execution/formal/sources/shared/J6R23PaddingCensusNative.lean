
import J6R23PaddingCensusMachine

/-! From the actual oriented address tape (the existing physical
placement, not a changed choice of packet order), produce all
integer pad loads at each of the original odd sites. -/
namespace J6R23PaddingCensus
open scoped BigOperators Classical
open P11FullPacking J6Mesh J6OrientedHost J6RecursiveOrientation
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape
set_option maxHeartbeats 17000000
set_option linter.unusedSectionVars false

private theorem bool_by_true (b c : Bool) (h : b=true ↔ c=true) : b=c := by
  cases b <;> cases c <;> simp_all

private theorem same_count {A D : Type*} (R : A→D→Prop)
    (x : A→Bool) (y : D→Bool) {l : List A} {k : List D}
    (h : List.Forall₂ R l k) (eq : ∀ a d,R a d→x a=y d) :
    l.countP x=k.countP y := by
  induction h with
  | nil => rfl
  | cons p ps ih => simp only [List.countP_cons,eq _ _ p,ih]

private theorem forall₂_map_count {A D E : Type*} (R : A→D→Prop)
    (f : A→E) (U : E→D→Prop) {l : List A} {k : List D}
    (h : List.Forall₂ R l k) (out : ∀ a d,R a d→U (f a) d) :
    List.Forall₂ U (l.map f) k := by
  induction h with
  | nil => exact .nil
  | cons p ps ih => exact .cons (out _ _ p) ih

section Native
variable {S : Type*} [LinearOrder S] [Fintype S] {K : ℕ}

abbrev NativePad (m l : ℕ) (w : Fin (a m)→S) := Pad w m (J6Mesh.K m) l

def realizesLayout (m l : ℕ) (mask : MaskFamily (a m) (J6Mesh.K m) S)
    (w : Fin (a m)→S) (hm : m≤J6Mesh.K m) (hL : 2*l=L m)
    (encodePage : Page (a m) (J6Mesh.K m) S→ℕ)
    (raw : List (PadColumnWord K (a m+1))) (order : List (NativePad m l w)) : Prop :=
  List.Forall₂ (fun word d =>
    word.represents encodePage (fun side=>oriented mask w m l hm hL (.inr (d,side))))
    raw order

def deltaWord (m : ℕ) (i : J6Recovery.Addr m) : Word (a m+1) :=
  natWord (a m+1) (index m i)

theorem delta_word_exact (m : ℕ) (i : J6Recovery.Addr m) :
    bitsValue (deltaWord m i).val=index m i := by
  change bitsValue (encodeBits (a m+1) (index m i))=_
  apply encodeBits_exact
  have h := (address_index m i).2.2.2
  have H : L m≤2^(a m+1) := by
    rw [J6Mesh.L,pow_succ]
    omega
  exact h.trans_le H

def censusAt (m : ℕ) (i : J6Recovery.Addr m) (raw : List (PadColumnWord K (a m+1))) :
    Meter (List (Fin 3)) :=
  let run := censusWords (deltaWord m i) raw
  ⟨run.result,run.steps+8*(a m+1)+8⟩

def censusBudget (K m C : ℕ) : ℕ :=
  13+8*(a m+1)+C*(15+C*tallyFee K (a m+1))

theorem census_at_exact
    (m l : ℕ) (mask : MaskFamily (a m) (J6Mesh.K m) S) (w : Fin (a m)→S)
    (hm : m≤J6Mesh.K m) (hL : 2*l=L m)
    (encodePage : Page (a m) (J6Mesh.K m) S→ℕ) (inj : Function.Injective encodePage)
    (raw : List (PadColumnWord K (a m+1))) (order : List (NativePad m l w))
    (nd : order.Nodup) (all : order.toFinset=Finset.univ)
    (chart : realizesLayout m l mask w hm hL encodePage raw order)
    (i : J6Recovery.Addr m) :
    List.Forall₂ (fun k d=>k.val=J6PhysicalInteger.loads m l mask w hm hL i d)
      (censusAt m i raw).result order ∧
    (censusAt m i raw).steps≤censusBudget K m order.length := by
  let R : PadColumnWord K (a m+1)→NativePad m l w→Prop :=
    fun u d=>u.represents encodePage (fun side=>oriented mask w m l hm hL (.inr (d,side)))
  let t := index m i
  let δ := deltaWord m i
  have tp : t<L m := (address_index m i).2.2.2
  have V : 2*L m≤2^(a m+1) := by simp [J6Mesh.L,pow_succ,Nat.mul_comm]
  have shift (u v : PadColumnWord K (a m+1)) (x y : NativePad m l w) (H : R u x) (Q : R v y) :
      (hitWord δ u v).result=padHit mask w hm hL t x y := by
    have e := (hit_word_exact (by omega) δ t (delta_word_exact m i) tp V encodePage inj
      _ _ u v H Q).1
    apply bool_by_true
    rw [e]
    simp only [padHit,Bool.or_eq_true,decide_eq_true_eq]
  have C := census_sweep_receipt (by omega : 0<a m+1) δ raw raw
  constructor
  · change List.Forall₂ _ (censusSweep δ raw raw).result order
    rw [C.1]
    refine forall₂_map_count R _ _ chart ?_
    intro v y rep
    have H := (count_hits_exact (by omega : 0<a m+1) δ v raw).1
    have e := same_count R (fun u=>(hitWord δ u v).result) (fun x=>padHit mask w hm hL t x y)
      chart (fun u x h=>shift u v x y h rep)
    rw [H,e,actual_pad_column_load m l mask w hm hL i order nd all]
    exact Nat.min_eq_right (J6R22RootReadout.source_padding_load_le_two m l mask w hm hL i y)
  · have c := C.2
    have len := (show List.Forall₂ R raw order from chart).length_eq
    change (censusSweep δ raw raw).steps+8*(a m+1)+8≤_
    simp only [len] at c
    unfold censusBudget
    omega
end Native

#print axioms delta_word_exact
#print axioms census_at_exact
end J6R23PaddingCensus
