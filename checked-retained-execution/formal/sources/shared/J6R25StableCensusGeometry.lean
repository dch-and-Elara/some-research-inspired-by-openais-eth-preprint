
import J6R23PaddingCensusNative
import J6R23PaddingCensusLegalChart

/-! Apply the already metered two-port census to a legal chart without
identifying its raw slot, shift, or load with any frozen layout. -/
namespace J6R25StableCensus
open scoped BigOperators Classical
open P11FullPacking J6Mesh J6OrientedHost J6R23PaddingCensus
open A1R10 A1R12 AOracleMachineTime
set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false

section Geometry
variable {S : Type*} [LinearOrder S] [Fintype S] {a b m l : ℕ}

theorem legal_pad_shift_iff (w : Fin a→S)
    (hm : m≤b) (hL : 2*l=2^a) (C : LegalRootChart w hm hL) (t : ℕ)
    (x y : Pad w m b l×Bool) :
    chartPadShift w hm hL C t x=some y ↔
      sameShift t (C.seats (.inr x)) (C.seats (.inr y)) := by
  rw [← chart_shift_iff w hm hL C t]
  unfold chartPadShift
  cases h : layoutShift w hm hL C t (.inr x) with
  | none => simp
  | some p =>
    cases p <;> simp

noncomputable def legalHit (w : Fin a→S)
    (hm : m≤b) (hL : 2*l=2^a) (C : LegalRootChart w hm hL) (t : ℕ)
    (src dst : Pad w m b l) : Bool :=
  let x := C.seats (.inr (src,false))
  decide (sameShift t x (C.seats (.inr (dst,false)))) ||
    decide (sameShift t x (C.seats (.inr (dst,true))))

theorem legal_hit_iff (w : Fin a→S)
    (hm : m≤b) (hL : 2*l=2^a) (C : LegalRootChart w hm hL) (t : ℕ)
    (x y : Pad w m b l) :
    legalHit w hm hL C t x y=true ↔
      J6OrientedPadding.incoming (chartPadShift w hm hL C t) (x,false)=some y := by
  unfold legalHit
  dsimp only
  simp only [Bool.or_eq_true,decide_eq_true_eq,← legal_pad_shift_iff w hm hL C t]
  unfold J6OrientedPadding.incoming
  simp only [Bool.false_eq_true,if_false]
  cases eq : chartPadShift w hm hL C t (x,false) with
  | none => simp
  | some p =>
    rcases p with ⟨d,side⟩
    cases side <;> simp

theorem legal_pad_hit_card (w : Fin a→S)
    (hm : m≤b) (hL : 2*l=2^a) (C : LegalRootChart w hm hL) (t : ℕ) (d : Pad w m b l) :
    (Finset.univ.filter (fun x : Pad w m b l => legalHit w hm hL C t x d=true)).card =
      J6OrientedPadding.count (chartPadShift w hm hL C t) d := by
  let u := Finset.univ.filter (fun x : Pad w m b l => legalHit w hm hL C t x d=true)
  let v := Finset.univ.filter (fun x : Pad w m b l×Bool =>
    J6OrientedPadding.incoming (chartPadShift w hm hL C t) x=some d)
  let E : (↥u)≃(↥v) :=
    { toFun := fun x=>⟨(x.val,false),Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(legal_hit_iff w hm hL C t x.val d).mp
          (Finset.mem_filter.mp x.property).2⟩⟩
      invFun := fun y=>⟨y.val.1,by
        have s := (Finset.mem_filter.mp y.property).2
        have q : y.val.2=false := by cases z : y.val.2 <;> simp [J6OrientedPadding.incoming,z] at s ⊢
        have e : (y.val.1,false)=y.val := Prod.ext rfl q.symm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(legal_hit_iff w hm hL C t _ _).mpr (e ▸ s)⟩⟩
      left_inv := fun x=>Subtype.ext rfl
      right_inv := fun y=>Subtype.ext (Prod.ext rfl (by
        have s := (Finset.mem_filter.mp y.property).2
        cases h : y.val.2 <;> simp [J6OrientedPadding.incoming,h] at s ⊢)) }
  change u.card=v.card
  simpa only [Fintype.card_coe] using Fintype.card_congr E
end Geometry

private theorem countP_card {T : Type*} [DecidableEq T] (p : T→Bool)
    (xs : List T) (nd : xs.Nodup) :
    xs.countP p=(xs.toFinset.filter (fun t=>p t=true)).card := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have good := List.nodup_cons.mp nd
    have hx : x∉xs.toFinset := by simpa using good.1
    rw [List.countP_cons,ih good.2,List.toFinset_cons,Finset.filter_insert]
    cases h : p x <;> simp [h,hx]

private theorem count_dec_irrel {D : Type*} [Fintype D] (d₁ d₂ : DecidableEq D)
    (f : D×Bool→Option (D×Bool)) (d : D) :
    @J6OrientedPadding.count D _ d₁ f d=@J6OrientedPadding.count D _ d₂ f d := by
  rw [Subsingleton.elim d₁ d₂]

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
variable {S : Type*} [LinearOrder S] [Fintype S] {Kp : ℕ}

theorem legal_loads_le_two (m l : ℕ) (w : Fin (a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) (d : NativePad m l w) :
    chartLoads m l w hm hL C i d≤2 := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  exact J6OrientedPadding.count_le_two _
    (chart_pad_partial_injective w hm hL C (index m i)) d

theorem actual_legal_pad_column_load (m l : ℕ) (w : Fin (a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (i : J6Recovery.Addr m) (order : List (NativePad m l w))
    (nd : order.Nodup) (all : order.toFinset=Finset.univ) (d : NativePad m l w) :
    order.countP (fun x=>legalHit w hm hL C (index m i) x d)=chartLoads m l w hm hL C i d := by
  rw [countP_card _ _ nd,all,legal_pad_hit_card]
  unfold chartLoads
  apply count_dec_irrel

def realizesLegalLayout (m l : ℕ) (w : Fin (a m)→S) (hm : m≤K m) (hL : 2*l=L m)
    (C : LegalRootChart w hm hL) (code : Page (a m) (K m) S→ℕ)
    (raw : List (PadColumnWord Kp (a m+1))) (order : List (NativePad m l w)) : Prop :=
  List.Forall₂ (fun row d=>row.represents code (fun side=>C.seats (.inr (d,side)))) raw order

theorem legal_census_at_exact
    (m l : ℕ) (w : Fin (a m)→S) (hm : m≤K m) (hL : 2*l=L m)
    (C : LegalRootChart w hm hL) (code : Page (a m) (K m) S→ℕ) (inj : Function.Injective code)
    (raw : List (PadColumnWord Kp (a m+1))) (order : List (NativePad m l w))
    (nd : order.Nodup) (all : order.toFinset=Finset.univ)
    (cert : realizesLegalLayout m l w hm hL C code raw order)
    (i : J6Recovery.Addr m) :
    List.Forall₂ (fun k d=>k.val=chartLoads m l w hm hL C i d)
      (censusAt m i raw).result order ∧
    (censusAt m i raw).steps≤censusBudget Kp m order.length := by
  let R : PadColumnWord Kp (a m+1)→NativePad m l w→Prop :=
    fun u d=>u.represents code (fun side=>C.seats (.inr (d,side)))
  let t := index m i
  let δ := deltaWord m i
  have tp : t<L m := (address_index m i).2.2.2
  have V : 2*L m≤2^(a m+1) := by simp [J6Mesh.L,pow_succ,Nat.mul_comm]
  have shift (u v : PadColumnWord Kp (a m+1)) (x y : NativePad m l w) (H : R u x) (Q : R v y) :
      (hitWord δ u v).result=legalHit w hm hL C t x y := by
    have e := (hit_word_exact (by omega) δ t (delta_word_exact m i) tp V code inj _ _ u v H Q).1
    apply bool_by_true
    rw [e]
    simp only [legalHit,Bool.or_eq_true,decide_eq_true_eq]
  have H := census_sweep_receipt (by omega : 0<a m+1) δ raw raw
  constructor
  · change List.Forall₂ _ (censusSweep δ raw raw).result order
    rw [H.1]
    refine forall₂_map_count R _ _ cert ?_
    intro v y rep
    have check := (count_hits_exact (by omega : 0<a m+1) δ v raw).1
    have e := same_count R (fun u=>(hitWord δ u v).result) (fun x=>legalHit w hm hL C t x y)
      cert (fun u x dc=>shift u v x y dc rep)
    rw [check,e,actual_legal_pad_column_load m l w hm hL C i order nd all]
    exact Nat.min_eq_right (legal_loads_le_two m l w hm hL C i y)
  · have bill := H.2
    have len := (show List.Forall₂ R raw order from cert).length_eq
    change (censusSweep δ raw raw).steps+8*(a m+1)+8≤_
    simp only [len] at bill
    unfold censusBudget
    omega
end Native

#print axioms legal_pad_shift_iff
#print axioms legal_hit_iff
#print axioms legal_pad_hit_card
#print axioms legal_loads_le_two
#print axioms actual_legal_pad_column_load
#print axioms legal_census_at_exact
end J6R25StableCensus
