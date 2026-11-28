import J6R10PacketAssembly
import J6R15SpecializedBoxNativeBase
import J6R11IntegralRetained

/-! Exact regrouping of the physical row and column *half*-ports inside
one original group. Both original ports remain present, even if their
two endpoints have the same group. -/
namespace J7R43Literal
open scoped BigOperators Classical
open P11FullPacking J6R9PacketScopes J6R9PacketChild J6R10Repack J6R11Integral
open J8Physical J8J9Grouped J6R14SpecializedBox
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {G R S V : Type} [LinearOrder G] {U : V→Type} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G U (2^a))
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G]
variable [∀ v, Fintype (U v)]
variable (mask : MaskFamily a b G) (i : Fin a)
variable (hr : ∀ w, rowGroup mask i (d.seat w)=d.rowLabel w.1)
variable (hc : ∀ w, colGroup mask i (d.seat w)=actualColLabel d w)
variable (g : G)

def extendRow (Y : RowBits d.seat mask i g) (w : Wire R) : Bool :=
  if h : rowGroup mask i (d.seat w)=g then Y ⟨w,h⟩ else false

def extendCol (X : ColBits d.seat mask i g) (w : Wire R) : Bool :=
  if h : colGroup mask i (d.seat w)=g then X ⟨w,h⟩ else false

theorem extendCol_at (X : ColBits d.seat mask i g) (w : Wire R)
    (h : colGroup mask i (d.seat w)=g) :
    extendCol d mask i g X w = X ⟨w,h⟩ := dif_pos h

include hr in
def rowLegEquiv : {w : Wire R // rowGroup mask i (d.seat w)=g} ≃ LocalRow d g × Bool where
  toFun w := (⟨w.val.1,(hr w.val).symm.trans w.prop⟩,w.val.2)
  invFun v := ⟨(v.1.val,v.2),(hr (v.1.val,v.2)).trans v.1.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hr in
def groupedRowEquiv : RowBits d.seat mask i g ≃ (LocalRow d g → Bool → Bool) :=
  ((rowLegEquiv d mask i hr g).arrowCongr (Equiv.refl Bool)).trans
    (Equiv.curry _ _ _)

include hc in
def groupedColEquiv : ColBits d.seat mask i g ≃ Assignment d g where
  toFun X := localLabels d g (extendCol d mask i g X)
  invFun x w := cubeLabels d (onlyGroup d g x) w.val
  left_inv X := by
    funext w
    let W := extendCol d mask i g X
    let C := fun k => localLabels d k W
    have hh : onlyGroup d g (localLabels d g W) g = C g := onlyGroup_here d g _
    have hp : actualColLabel d w.val = g := (hc w.val).symm.trans w.prop
    have h := cube_bit_owned d g _ C hh w.val hp
    rw [localLabels_cube d W w.val] at h
    exact h.trans (extendCol_at d mask i g X w.val w.prop)
  right_inv x := by
    let W := cubeLabels d (onlyGroup d g x)
    have hown (w : Wire R) (h : colGroup mask i (d.seat w)=g) :
        extendCol d mask i g (fun q => W q.val) w = W w :=
      extendCol_at d mask i g _ w h
    calc
      _ = localLabels d g W := by
        apply Prod.ext
        · funext s
          exact hown (pinWire d s.val) ((hc _).trans ((pinWire_colLabel d s.val).trans s.prop))
        · funext v j
          apply hown
          rw [hc]
          simpa only [actualColLabel, ordinaryWire_column] using v.prop
      _ = x := (cubeLabels_local d _ g).trans (onlyGroup_here d g x)

include hr hc in
def groupedPhysicalStateEquiv :
    State d.seat d.seat mask i g ≃ (LocalRow d g → Bool → Bool) × Assignment d g :=
  Equiv.prodCongr (groupedRowEquiv d mask i hr g) (groupedColEquiv d mask i hc g)

include hr in
theorem grouped_row_reads (Y : RowBits d.seat mask i g) (r : LocalRow d g) (leg : Bool) :
    groupedRowEquiv d mask i hr g Y r leg = extendRow d mask i g Y (r.val,leg) := by
  rw [extendRow,dif_pos ((hr (r.val,leg)).trans r.prop)]
  rfl

include hr in
theorem actual_row_packet_product {K : Type*} [CommMonoid K] (φ : Wire R → K) :
    (∏ k : Page a b G, ∏ w ∈ J6R10PacketAssembly.actualRows
      (fun w : Wire R => (rowBlock mask i (d.seat w)).swap) g k, φ w) =
    ∏ r : LocalRow d g, ∏ leg : Bool, φ (r.val,leg) := by
  let selected := Finset.univ.filter (fun w : Wire R => rowGroup mask i (d.seat w)=g)
  calc
    _ = ∏ w ∈ selected, φ w := by
      rw [← Finset.prod_fiberwise selected (fun w => (d.seat w).1) φ]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      refine Finset.prod_congr ?_ (fun _ _ => rfl)
      ext w
      simp [selected,J6R10PacketAssembly.actualRows,rowBlock,and_comm,rowGroup]
    _ = ∏ w : {w : Wire R // rowGroup mask i (d.seat w)=g}, φ w.val := by
      let e : {w // w ∈ selected} ≃ {w : Wire R // rowGroup mask i (d.seat w)=g} :=
        Equiv.subtypeEquivRight (fun w => by simp [selected])
      exact (Finset.prod_coe_sort selected φ).symm.trans
        (Fintype.prod_equiv e (fun x => φ x.val) (fun x => φ x.val) (fun _ => rfl))
    _ = ∏ r : LocalRow d g, ∏ leg : Bool, φ (r.val,leg) := by
      let f : LocalRow d g × Bool → K := fun p => φ (p.1.val,p.2)
      exact (Fintype.prod_equiv (rowLegEquiv d mask i hr g) _ f (fun _ => rfl)).trans
        (Fintype.prod_prod_type f)

#print axioms extendCol_at
#print axioms rowLegEquiv
#print axioms groupedColEquiv
#print axioms groupedPhysicalStateEquiv
#print axioms grouped_row_reads
#print axioms actual_row_packet_product
end
end J7R43Literal