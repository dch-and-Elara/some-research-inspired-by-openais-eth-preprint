import V8NativeMessageN6MainFiberGeometry
import V8NativeMessageN6MainFiberWords

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14000000

/-! Compile the actual N2 frame directly from the original per-copy
exceptional rows and the four-clone incidence placement. This is the
printed column restriction, including all zero rows. -/
namespace V8NativeMessage.N6.MainFiber
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N1
open P5MainIterator P5MainBalance P5MainBalance.M6
open scoped BigOperators Classical

noncomputable section
variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q : ℕ}
variable {hreg : ∀ v,GraphCutMoments.degree F v=3}

def rowAt (keep : ℕ→Prop) :
    Fin (Fintype.card (Row keep Copy r Q)) ≃ Row keep Copy r Q :=
  (Fintype.equivFin _).symm

def sourceFrame (keep : ℕ→Prop) (P : Seating F Copy r Q hreg)
    (t : Fin Q) (E : Finset (Clone W)) (y : Fin r→Row keep Copy r Q→ℤ) :
    Frame (Clone W) (Fin r) where
  group v := P.variableLabel v t
  rows _ := Fintype.card (Row keep Copy r Q)
  C _ j v := rowCoefficient keep P (rowAt keep j) v.val
  y g j := y g (rowAt keep j)
  E := E

theorem source_frame_positive (keep : ℕ→Prop) (h0 : keep 0)
    (P : Seating F Copy r Q hreg) (t : Fin Q) (E : Finset (Clone W))
    (y : Fin r→Row keep Copy r Q→ℤ) :
    positiveCover (sourceFrame keep P t E y) := by
  intro g v
  obtain ⟨o,hn,hp⟩ := zeroRow_has_positive_cover keep h0 P v.val
  let j := ((rowAt (Copy:=Copy) (r:=r) (Q:=Q) keep).symm (zeroRow keep h0 o))
  have he : rowAt (Copy:=Copy) (r:=r) (Q:=Q) keep j=zeroRow keep h0 o :=
    Equiv.apply_symm_apply _ _
  refine ⟨j,fun w=>?_,?_⟩
  · change 0≤rowCoefficient keep P (rowAt keep j) w.val
    rw [he]
    exact hn w.val
  · change 0<rowCoefficient keep P (rowAt keep j) v.val
    rw [he]
    exact hp

theorem source_frame_measure (keep : ℕ→Prop) (P : Seating F Copy r Q hreg)
    (t : Fin Q) (E : Finset (Clone W)) (y : Fin r→Row keep Copy r Q→ℤ)
    (g : Fin r) (j : Fin (Fintype.card (Row keep Copy r Q))) (x : Clone W→Bool) :
    V8NativeMessage.C3.NativeAssembly.MainScan.measure (sourceFrame keep P t E y) g (fun v=>x v.val) j =
      integerCoordinate keep P.layout t x g (rowAt keep j) := by
  let s := (Finset.univ : Finset (Clone W)).filter (fun v=>P.variableLabel v t=g)
  let f : Clone W→ℤ := fun v => rowCoefficient keep P (rowAt keep j) v *
    (if x v then 1 else 0)
  calc
    _ = ∑ v : {v : Clone W // P.variableLabel v t=g},f v.val := by
      unfold V8NativeMessage.C3.NativeAssembly.MainScan.measure
      apply Finset.sum_congr (by ext v; simp)
      intro v _
      rfl
    _ = ∑ v∈s,f v := (Finset.sum_subtype s (fun v=>by simp [s]) f).symm
    _ = _ := by
      unfold s
      rw [Finset.sum_filter]
      unfold integerCoordinate
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : P.variableLabel v t=g
      · cases hx : x v <;> simp [f,hv,hx,rowCoefficient,Seating.layout]
      · simp [f,hv,Seating.layout]

def allOneAddress (keep : ℕ→Prop) (P : Seating F Copy r Q hreg)
    (t : Fin Q) (g : Fin r) (j : Row keep Copy r Q) : ℤ :=
  integerCoordinate keep P.layout t (fun _=>true) g j

theorem zero_source_target (keep : ℕ→Prop) (P : Seating F Copy r Q hreg)
    (t : Fin Q) (E : Finset (Clone W)) :
    zeroTarget (sourceFrame keep P t E (fun _ _=>0)) := fun _ _=>rfl

theorem one_source_target (keep : ℕ→Prop) (P : Seating F Copy r Q hreg)
    (t : Fin Q) (E : Finset (Clone W)) :
    oneTarget (sourceFrame keep P t E (allOneAddress keep P t)) := by
  intro g j
  change allOneAddress keep P t g (rowAt keep j) =
    V8NativeMessage.C3.NativeAssembly.MainScan.measure (sourceFrame keep P t E (allOneAddress keep P t)) g (fun _=>true) j
  exact (source_frame_measure keep P t E (allOneAddress keep P t) g j (fun _=>true)).symm

omit [Fintype Copy] in
theorem one_address_in_printed_box (keep : ℕ→Prop) (P : Seating F Copy r Q hreg)
    (t : Fin Q) (g : Fin r) (j : Row keep Copy r Q) :
    |allOneAddress keep P t g j|≤((r^(2*Q):ℕ):ℤ) := by
  have h := integer_coordinate_exact_D keep P.layout t g (fun _=>true) j
  rwa [card_wordCells,Fintype.card_fin,Fintype.card_fin] at h

#print axioms rowAt
#print axioms sourceFrame
#print axioms source_frame_positive
#print axioms source_frame_measure
#print axioms zero_source_target
#print axioms one_source_target
#print axioms one_address_in_printed_box

end
end V8NativeMessage.N6.MainFiber
