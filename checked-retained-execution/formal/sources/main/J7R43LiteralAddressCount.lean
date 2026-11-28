import J7R43LiteralAnchor
import J7R43LiteralRequests
import J9R20SameFileHighAnchors

/-! Distinct physical request addresses, not just a cardinality of an
indexing type. Different occupied tiles have distinct (page,parity), and
different orders within one tile have distinct full singleton tuples. -/
namespace J7R43Literal
open scoped Classical
open P11FullPacking J6R9PacketScopes J8Physical J6R14SpecializedBox
open J9R17AllPins J9R20SameFile
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4700000
local instance (priority := 17000) j7CountPageEq (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)

variable {R S V : Type} {U : V→Type} {a b p : ℕ} [Fintype S]
variable (d : Layout (Page a b (Fin 64)) R S V (Fin 64) U (2^a))
variable (mask : MaskFamily a b (Fin 64)) (i : Fin a)
variable (hr : ∀ w, rowGroup mask i (d.seat w)=d.rowLabel w.1)
variable (hc : ∀ w, colGroup mask i (d.seat w)=actualColLabel d w)
variable (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
variable (legal : ∀ w : Orders d, w.2.val < p-1)

def actualIndividualMode (w : Orders d) : Mode i p mask :=
  anchoredMode d mask i hr hc (anchor d w.1) (off _) ⟨w.2.val,legal w⟩

theorem physical_modes_distinct (hi : i.val=0) :
    Function.Injective (actualIndividualMode d mask i hr hc off legal) := by
  intro x y h
  let s := anchor d x.1
  let t := anchor d y.1
  let mx := actualIndividualMode d mask i hr hc off legal x
  let my := actualIndividualMode d mask i hr hc off legal y
  change mx=my at h
  have hx := singleton_address_same_tile d mask i hr hc hi s (off s) ⟨x.2.val,legal x⟩
  have hy := singleton_address_same_tile d mask i hr hc hi t (off t) ⟨y.2.val,legal y⟩
  have hp : (tileKey d s).1=(tileKey d t).1 := by
    exact hx.1.symm.trans ((congrArg (fun m : Mode i p mask => m.page) h).trans hy.1)
  have hq : (tileKey d s).2.val=(tileKey d t).2.val := by
    exact hx.2.1.symm.trans ((congrArg (fun m : Mode i p mask => m.tile.val) h).trans hy.2.1)
  have tk : tileKey d s = tileKey d t := Prod.ext hp (Fin.ext hq)
  have oldX : tileKey d s = x.1.val := congrArg Subtype.val (anchor_holds d x.1)
  have oldY : tileKey d t = y.1.val := congrArg Subtype.val (anchor_holds d y.1)
  have eqFst : x.1=y.1 := Subtype.ext (oldX.symm.trans (tk.trans oldY))
  have eqOrd : x.2.val=y.2.val :=
    hx.2.2.1.symm.trans ((congrArg (fun m : Mode i p mask => m.order.val) h).trans hy.2.2.1)
  obtain ⟨k,n⟩ := x
  obtain ⟨k',n'⟩ := y
  change k=k' at eqFst
  subst k'
  have eqN : n=n' := Fin.ext eqOrd
  subst n'
  rfl

def genuineRequest (hp : 0<p) : WithBaselines d→PublicMenu mask i p × Fin 64
  | .inl g => (⟨0,J6RecursiveMenu.zero_in_menu p hp _ (fun m => m.order.val.succ_pos)⟩,g)
  | .inr w =>
    (publicAnchoredMenu d mask i hr hc (anchor d w.1) (off _) ⟨w.2.val,legal w⟩,
      d.pinLabel (anchor d w.1))

theorem genuine_requests_distinct (hi : i.val=0) (hp : 0<p) :
    Function.Injective (genuineRequest d mask i hr hc off legal hp) := by
  intro x y he
  cases x with
  | inl g =>
    cases y with
    | inl g' =>
      exact congrArg Sum.inl (congrArg Prod.snd he)
    | inr w =>
      have hh := congrArg (fun z : PublicMenu mask i p × Fin 64 => z.1.val.support.card) he
      change (Finsupp.support (0:Mode i p mask→₀ℕ)).card =
        (publicAnchoredMenu d mask i hr hc (anchor d w.1) (off _) ⟨w.2.val,legal w⟩).val.support.card at hh
      rw [Finsupp.support_zero,Finset.card_empty,
        public_anchored_support d mask i hr hc _ _ _] at hh
      omega
  | inr w =>
    cases y with
    | inl g =>
      have hh := congrArg (fun z : PublicMenu mask i p × Fin 64 => z.1.val.support.card) he
      change (publicAnchoredMenu d mask i hr hc (anchor d w.1) (off _) ⟨w.2.val,legal w⟩).val.support.card =
        (Finsupp.support (0:Mode i p mask→₀ℕ)).card at hh
      rw [Finsupp.support_zero,Finset.card_empty,
        public_anchored_support d mask i hr hc _ _ _] at hh
      omega
    | inr w' =>
      apply congrArg Sum.inr
      apply physical_modes_distinct d mask i hr hc off legal hi
      have hh := congrArg (fun z : PublicMenu mask i p × Fin 64 => z.1.val.support) he
      change (Finsupp.single (actualIndividualMode d mask i hr hc off legal w) (1:ℕ)).support =
        (Finsupp.single (actualIndividualMode d mask i hr hc off legal w') (1:ℕ)).support at hh
      simpa only [Finsupp.support_single_ne_zero _ (one_ne_zero : (1:ℕ)≠0),Finset.singleton_inj] using hh

#print axioms actualIndividualMode
#print axioms physical_modes_distinct
#print axioms genuineRequest
#print axioms genuine_requests_distinct
end
end J7R43Literal
