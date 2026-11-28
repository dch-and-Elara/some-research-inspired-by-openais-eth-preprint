
import J6R22RootReadoutNativeFactor

/-! The two actual target ports of each padding column, with the
one original negative row per padding gadget. This is the printed
nonwrapping physical shift, not an adjacency shortcut. -/
namespace J6R23PaddingCensus
open scoped BigOperators Classical
open P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6RecursiveOrientation J6RecursiveOrientationLocal
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000

def sameShift {P : Type*} {L : ℕ} (t : ℕ) (p q : P×Fin L) : Prop :=
  p.1=q.1 ∧ p.2.val+t=q.2.val

variable {S : Type*} [LinearOrder S] [Fintype S] {a b m l : ℕ}

theorem actual_shift_iff (mask : MaskFamily a b S) (w : Fin a→S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ)
    (x y : Wire w m b l) :
    shifted mask w m l h hL t x=some y ↔
      sameShift t (oriented mask w m l h hL x) (oriented mask w m l h hL y) := by
  constructor
  · exact exact_shift mask w m l h hL t x y
  · intro H
    let e := placement mask w m l h hL
    have Y : (e x).1=(e y).1 ∧ (e x).2.val+t=(e y).2.val := H
    have legal : (e x).2.val+t<2^a := Y.2 ▸ (e y).2.isLt
    change (if ht : (e x).2.val+t<2^a then some (e.symm ((e x).1,⟨(e x).2.val+t,ht⟩))
      else none)=some y
    rw [dif_pos legal]
    apply congrArg some
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext Y.1 (Fin.ext Y.2)

theorem actual_pad_shift_iff (mask : MaskFamily a b S) (w : Fin a→S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ)
    (x y : Pad w m b l×Bool) :
    padShift mask w h hL t x=some y ↔
      sameShift t (oriented mask w m l h hL (.inr x)) (oriented mask w m l h hL (.inr y)) := by
  rw [← actual_shift_iff mask w h hL t]
  constructor
  · exact padShift_apply mask w h hL t x y
  · intro H
    unfold padShift
    rw [H]
    rfl

noncomputable def padHit (mask : MaskFamily a b S) (w : Fin a→S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ) (x y : Pad w m b l) : Bool :=
  let A := oriented mask w m l h hL (.inr (x,false))
  decide (sameShift t A (oriented mask w m l h hL (.inr (y,false)))) ||
    decide (sameShift t A (oriented mask w m l h hL (.inr (y,true))))

theorem pad_hit_iff_incoming (mask : MaskFamily a b S) (w : Fin a→S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ) (x y : Pad w m b l) :
    padHit mask w h hL t x y=true ↔
      J6OrientedPadding.incoming (padShift mask w h hL t) (x,false)=some y := by
  unfold padHit
  dsimp only
  simp only [Bool.or_eq_true,decide_eq_true_eq,← actual_pad_shift_iff mask w h hL t]
  unfold J6OrientedPadding.incoming
  simp only [Bool.false_eq_true,if_false]
  cases eq : padShift mask w h hL t (x,false) with
  | none => simp
  | some p =>
    rcases p with ⟨d,side⟩
    cases side <;> simp

theorem physical_pad_hit_card (mask : MaskFamily a b S) (w : Fin a→S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ) (d : Pad w m b l) :
    (Finset.univ.filter (fun x : Pad w m b l => padHit mask w h hL t x d=true)).card =
      J6OrientedPadding.count (padShift mask w h hL t) d := by
  let u := Finset.univ.filter (fun x : Pad w m b l => padHit mask w h hL t x d=true)
  let v := Finset.univ.filter (fun x : Pad w m b l×Bool =>
    J6OrientedPadding.incoming (padShift mask w h hL t) x=some d)
  let E : (↥u)≃(↥v) :=
    { toFun := fun x=>⟨(x.val,false),Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(pad_hit_iff_incoming mask w h hL t x.val d).mp
          (Finset.mem_filter.mp x.property).2⟩⟩
      invFun := fun y=>⟨y.val.1,by
        have s := (Finset.mem_filter.mp y.property).2
        have q : y.val.2=false := by cases z : y.val.2 <;> simp [J6OrientedPadding.incoming,z] at s ⊢
        have e : (y.val.1,false)=y.val := Prod.ext rfl q.symm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(pad_hit_iff_incoming mask w h hL t _ _).mpr (e ▸ s)⟩⟩
      left_inv := fun x=>Subtype.ext rfl
      right_inv := fun y=>Subtype.ext (Prod.ext rfl (by
        have s := (Finset.mem_filter.mp y.property).2
        cases h : y.val.2 <;> simp [J6OrientedPadding.incoming,h] at s ⊢)) }
  change u.card=v.card
  simpa only [Fintype.card_coe] using Fintype.card_congr E

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

theorem actual_pad_column_load {S : Type*} [LinearOrder S] [Fintype S]
    (m l : ℕ) (mask : MaskFamily (J6Mesh.a m) (K m) S) (w : Fin (J6Mesh.a m)→S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m)
    (order : List (Pad w m (K m) l)) (nodup : order.Nodup) (all : order.toFinset=Finset.univ)
    (d : Pad w m (K m) l) :
    order.countP (fun x=>padHit mask w hm hL (index m i) x d) = J6PhysicalInteger.loads m l mask w hm hL i d := by
  rw [countP_card _ _ nodup,all,physical_pad_hit_card]
  unfold J6PhysicalInteger.loads
  apply count_dec_irrel

#print axioms actual_shift_iff
#print axioms actual_pad_shift_iff
#print axioms pad_hit_iff_incoming
#print axioms physical_pad_hit_card
#print axioms actual_pad_column_load
end J6R23PaddingCensus
