import J6R15SpecializedBoxNativeBase
import J6R14SpecializedBoxModeChart

/-! Reindex the two independent retained half-port cubes of a genuine
packet child. Its row and column bits remain independent. The former
are the two legs of each actual subdivision row; the latter are
precisely the original local pin and old-column variables. -/
namespace J6R14SpecializedBox
open scoped Classical BigOperators
open P11FullPacking J6R9PacketChild J6R9PacketScopes J8Physical J8J9Grouped

noncomputable section
set_option linter.unusedSectionVars false
variable {G R S V : Type*} [LinearOrder G] {P : V→Type*} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G P (2^a))
variable (mask : MaskFamily a b G) (i : Fin a)
variable (hr : ∀ x, rowGroup mask i (d.seat x) = d.rowLabel x.1)
variable (hc : ∀ x, colGroup mask i (d.seat x) = actualColLabel d x)

def rowHalfChart (g : G) :
    {w : Wire R // rowGroup mask i (d.seat w)=g} ≃ LocalRow d g × Bool where
  toFun w := (⟨w.val.1,(hr w.val).symm.trans w.prop⟩,w.val.2)
  invFun v := ⟨(v.1.val,v.2),(hr _).trans v.1.prop⟩
  left_inv w := by rcases w with ⟨⟨r,j⟩,h⟩; rfl
  right_inv w := by rcases w with ⟨⟨r,h⟩,j⟩; rfl

def rowAssignmentEquiv (g : G) :
    RowBits d.seat mask i g ≃ (LocalRow d g→Bool→Bool) :=
  ((rowHalfChart d mask i hr g).arrowCongr (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def oldActualGroup (g : G) (v : LocalColumn d g) (n : P v.val) :
    actualColLabel d (ordinaryWire d ⟨v.val,n⟩)=g := by
  unfold actualColLabel
  rw [ordinaryWire_column]
  exact v.prop

def readColumn (g : G) (y : ColBits d.seat mask i g) : J8J9Grouped.Assignment d g :=
  (fun p => y ⟨pinWire d p.val, (hc _).trans ((pinWire_colLabel d p.val).trans p.prop)⟩,
   fun v n => y ⟨ordinaryWire d ⟨v.val,n⟩,(hc _).trans (oldActualGroup d g v n)⟩)

def extendColumns (g : G) (y : ColBits d.seat mask i g) : Wire R→Bool :=
  fun w => if h : colGroup mask i (d.seat w)=g then y ⟨w,h⟩ else false

theorem readColumn_extended (g : G) (y : ColBits d.seat mask i g) :
    readColumn d mask i hc g y = localLabels d g (extendColumns d mask i g y) := by
  apply Prod.ext
  · funext p
    unfold readColumn localLabels extendColumns
    dsimp only
    split
    · rfl
    · rename_i hf
      exact (hf ((hc _).trans ((pinWire_colLabel d _).trans p.prop))).elim
  · funext v n
    unfold readColumn localLabels extendColumns
    dsimp only
    split
    · rfl
    · rename_i hf
      exact (hf ((hc _).trans (by first | exact (pinWire_colLabel d _).trans p.prop | exact oldActualGroup d g v n))).elim

variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype (Page a b G)]
variable [DecidableEq (Page a b G)] [(v : V)→Fintype (P v)] [(v : V)→DecidableEq (P v)]

def colAssignmentEquiv (g : G) :
    ColBits d.seat mask i g ≃ J8J9Grouped.Assignment d g where
  toFun := readColumn d mask i hc g
  invFun A w := cubeLabels d (onlyGroup d g A) w.val
  left_inv y := by
    funext w
    let X := extendColumns d mask i g y
    have hA : onlyGroup d g (readColumn d mask i hc g y) g = localLabels d g X :=
      (onlyGroup_here d g _).trans (readColumn_extended d mask i hc g y)
    have hw : actualColLabel d w.val=g := (hc w.val).symm.trans w.prop
    change cubeLabels d (onlyGroup d g (readColumn d mask i hc g y)) w.val = _
    rw [cube_bit_owned d g _ (fun i => localLabels d i X) hA w.val hw,localLabels_cube]
    exact dif_pos w.prop
  right_inv A := by
    change localLabels d g (cubeLabels d (onlyGroup d g A)) = A
    rw [cubeLabels_local,onlyGroup_here]

def physicalGroupState (g : G) :
    (RowBits d.seat mask i g × ColBits d.seat mask i g) ≃
      ((LocalRow d g→Bool→Bool) × J8J9Grouped.Assignment d g) :=
  (rowAssignmentEquiv d mask i hr g).prodCongr (colAssignmentEquiv d mask i hc g)

#print axioms rowHalfChart
#print axioms rowAssignmentEquiv
#print axioms readColumn_extended
#print axioms colAssignmentEquiv
#print axioms physicalGroupState
end
end J6R14SpecializedBox