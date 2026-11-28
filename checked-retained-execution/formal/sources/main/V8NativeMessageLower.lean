import V8NativeMessageReceive
import V8NativeMessageMatchCount

/-! The actual same-CNF C2/N8 lower bound. The matching certificate
crosses the frozen group union; the receiver already knows its own
active bits. This is a row-information bound, not a value-range bound. -/
namespace V8NativeMessage.Five
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive
open V8PooledMenu V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2300000

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G}
  {f : ℤ[X]} {m : ℕ} (K : Pairs G m)
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
  (i : Fin (rootU V)) (T : Finset (Fin 64))

structure Crosses where
  left : ∀ j, switchGroup P (physIndex i) (K.seat (j,false))∈T
  right : ∀ j, switchGroup P (physIndex i) (K.seat (j,true))∉T

def matchRow (x : Fin m → Bool) : RowWords P i T :=
  fun v => activeSigns K x (fun _ => false) v.val

def matchCol (y : Fin m → Bool) : ColWords P i T :=
  fun v => activeSigns K (fun _ => false) y v.val

theorem matchSigns (cross : Crosses K P i T) (x y : Fin m → Bool) :
    signs P i T (matchRow K P i T x) (matchCol K P i T y)=activeSigns K x y := by
  funext v
  by_cases hv : v∈Set.range K.seat
  · obtain ⟨⟨j,b⟩,rfl⟩ := hv
    cases b
    · simp only [signs,dif_pos (cross.left j),matchRow,activeSigns_left]
    · simp only [signs,dif_neg (cross.right j),matchCol,activeSigns_right]
  · by_cases ht : switchGroup P (physIndex i) v∈T
    · simp only [signs,dif_pos ht,matchRow,activeSigns,liftPairs_off K _ v hv]
    · simp only [signs,dif_neg ht,matchCol,activeSigns,liftPairs_off K _ v hv]

variable (L : PublicPrecision V) (probes : Probes V f) (hf : f.Monic)
  (hd : 0<f.natDegree) (cross : Crosses K P i T)

include hd cross in
theorem matched_receiver (x y : Fin m → Bool) :
    fixedNative P hu huM i L probes hf (activeSigns K x y)=
      rowDecoder P hu huM i T L probes
        (rowMessage P hu huM i T L (matchRow K P i T x)) (matchCol K P i T y) := by
  rw [← matchSigns K P i T cross]
  exact N8_native P hu huM i T L probes hf hd _ _

include hd cross in
/-- Extra information here is a row-only b-bit word. Column-only
information is already included in the receiver's true column view. -/
theorem N8_needs_bits {b : ℕ} (aux : (Fin m → Bool) → Fin b → Bool)
    (dec : (Fin m → Bool) → (Fin b → Bool) → FixedMenu P hu huM i L f → ZMod 2)
    (correct : ∀ x y, dec y (aux x) (fixedNative P hu huM i L probes hf (activeSigns K x y))=
      (originCount G p (activeSigns K x y):ZMod 2)) :
    m≤fixedBits (rootA V) i (L.prec i)+b := by
  let msg (x : Fin m → Bool) : RowTape hu huM i L × (Fin b → Bool) :=
    (rowMessage P hu huM i T L (matchRow K P i T x),aux x)
  have inj : Function.Injective msg := by
    intro x x' h
    have hrow := congrArg Prod.fst h
    have haux := congrArg Prod.snd h
    have hm : fixedNative P hu huM i L probes hf (activeSigns K x x)=
        fixedNative P hu huM i L probes hf (activeSigns K x' x) := by
      rw [matched_receiver K P hu huM i T L probes hf hd cross,
        matched_receiver K P hu huM i T L probes hf hd cross]
      exact congrArg (fun z => rowDecoder P hu huM i T L probes z (matchCol K P i T x)) hrow
    by_contra hn
    have e := (correct x x).symm.trans ((congrArg₂ (dec x) haux hm).trans (correct x' x))
    rw [C2_parity K p x x,C2_parity K p x' x,if_pos rfl,if_neg (Ne.symm hn)] at e
    exact one_ne_zero e
  have hc := Fintype.card_le_of_injective msg inj
  rw [Fintype.card_prod,N8_row_alphabet hu huM i L] at hc
  apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  simpa [Fintype.card_fun,Fintype.card_bool,pow_add] using hc

include hd cross in
theorem N8_some_failure {b : ℕ} (aux : (Fin m → Bool) → Fin b → Bool)
    (dec : (Fin m → Bool) → (Fin b → Bool) → FixedMenu P hu huM i L f → ZMod 2)
    (small : fixedBits (rootA V) i (L.prec i)+b<m) :
    ∃ x y, dec y (aux x) (fixedNative P hu huM i L probes hf (activeSigns K x y))≠
      (originCount G p (activeSigns K x y):ZMod 2) := by
  by_contra! h
  exact (not_le_of_gt small) (N8_needs_bits K P hu huM i T L probes hf hd cross aux dec h)

#print axioms matchSigns
#print axioms matched_receiver
#print axioms N8_needs_bits
#print axioms N8_some_failure
end
end V8NativeMessage.Five
