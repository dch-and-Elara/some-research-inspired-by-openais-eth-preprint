import AAcquisitionCostSeats
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card

/-! A4 finite occupancy: given the planted hard-port injection and exact
full diagonal cell size, fit all designated pairs as real consecutive
even/odd seats, then fill the leftover seats bijectively. -/
namespace A4R45PairSeats
open AAcquisitionCost
set_option autoImplicit false
set_option warningAsError true

theorem extend_finite_pair_embedding {A W V : Type*}
    [Fintype A] [Fintype W] [Fintype V]
    (hard : A ↪ W) (seats : A ↪ V) (total : Fintype.card W=Fintype.card V) :
    ∃ full : W ≃ V, ∀ a, full (hard a)=seats a := by
  classical
  let s : Set W := Set.range hard
  let t : Set V := Set.range seats
  letI : Fintype s := Fintype.ofFinite _
  letI : Fintype t := Fintype.ofFinite _
  letI : Fintype (sᶜ : Set W) := Fintype.ofFinite _
  letI : Fintype (tᶜ : Set V) := Fintype.ofFinite _
  let aW : A ≃ s := Equiv.ofInjective hard hard.injective
  let aV : A ≃ t := Equiv.ofInjective seats seats.injective
  let planted : s ≃ t := aW.symm.trans aV
  have hcard : Fintype.card (sᶜ : Set W) = Fintype.card (tᶜ : Set V) := by
    rw [Fintype.card_compl_set s, Fintype.card_compl_set t, total, Fintype.card_congr planted]
  let spare : (sᶜ : Set W) ≃ (tᶜ : Set V) := Fintype.equivOfCardEq hcard
  refine ⟨(Equiv.Set.sumCompl s).symm.trans ((Equiv.sumCongr planted spare).trans
    (Equiv.Set.sumCompl t)), ?_⟩
  intro a
  have hs : hard a ∈ s := ⟨a,rfl⟩
  simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hs]
  change (aV (aW.symm ⟨hard a,hs⟩)).val = seats a
  change (aV (aW.symm (aW a))).val = seats a
  rw [Equiv.symm_apply_apply]
  rfl

def pairSeat {copies half : ℕ} (x : (Fin copies × Fin half) × Bool) :
    Fin copies × Fin (2*half) :=
  (x.1.1, ⟨2*x.1.2.val+(if x.2 then 1 else 0), by
    have hi := x.1.2.isLt
    cases x.2 <;> simp only [Bool.false_eq_true,if_true,if_false] <;> omega⟩)

theorem pairSeat_injective (copies half : ℕ) :
    Function.Injective (pairSeat (copies:=copies) (half:=half)) := by
  rintro ⟨⟨p,i⟩,a⟩ ⟨⟨q,j⟩,b⟩ eq
  have pq := congrArg Prod.fst eq
  change p=q at pq
  have hi := congrArg (fun z : Fin copies × Fin (2*half) => z.2.val) eq
  change 2*i.val+(if a then 1 else 0)=2*j.val+(if b then 1 else 0) at hi
  have ab : a=b := by cases a <;> cases b <;> simp_all <;> omega
  subst b
  have ij : i=j := Fin.ext (by cases a <;> simp_all)
  subst q
  subst j
  rfl

theorem full_diagonal_pair_seating {A W : Type*} [Fintype A] [Fintype W]
    (copies half : ℕ) (hard : A × Bool ↪ W)
    (room : Fintype.card A ≤ copies*half)
    (full : Fintype.card W = copies*(2*half)) :
    ∃ seat : W ≃ (Fin copies × Fin (2*half)), ∀ a,
      wirePred seat (hard (a,true))=some (hard (a,false)) := by
  classical
  let pick : A ↪ (Fin copies × Fin half) :=
    { toFun := fun a => finProdFinEquiv.symm (Fin.castLE room (Fintype.equivFin A a))
      inj' := fun a b h => (Fintype.equivFin A).injective
        (Fin.ext (congrArg (fun z : Fin (copies*half) => z.val) (finProdFinEquiv.symm.injective h))) }
  let insert : A×Bool ↪ (Fin copies × Fin (2*half)) :=
    { toFun := fun a => pairSeat (pick a.1,a.2)
      inj' := fun x y h =>
        have eq := pairSeat_injective copies half h
        Prod.ext (pick.injective (congrArg (fun z : (Fin copies × Fin half) × Bool => z.1) eq))
          (congrArg (fun z : (Fin copies × Fin half) × Bool => z.2) eq) }
  have card : Fintype.card W = Fintype.card (Fin copies × Fin (2*half)) := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using full
  obtain ⟨seat, agrees⟩ := extend_finite_pair_embedding hard insert card
  refine ⟨seat, fun a => (wirePred_spec seat _ _).mpr ?_⟩
  unfold packetOf positionOf
  rw [agrees (a,true), agrees (a,false)]
  constructor
  · rfl
  · change ((2*(pick a).2.val:ℕ):ℤ)+1 = ((2*(pick a).2.val+1:ℕ):ℤ)
    push_cast
    rfl

#print axioms extend_finite_pair_embedding
#print axioms pairSeat_injective
#print axioms full_diagonal_pair_seating
end A4R45PairSeats
