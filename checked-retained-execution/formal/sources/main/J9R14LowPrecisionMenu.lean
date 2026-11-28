import J9R14LowPrecisionComplete

/-!
# Complete projected mode menus at the physical outer node

Every legal allocation is selected by its actual Finsupp exponent,
without an externally supplied coefficient or a port-allocation
lookup. A positive-arity original equality owner supplies one
representative port for the guard reindexing proof.
-/

namespace J9R14LowPrecisionMenu
open scoped Polynomial BigOperators Classical
open DenominatorBudget P11FullPacking OuterNodePacking J6R9PacketScopes
open J9R14LowPrecisionGeometry J9R14LowPrecisionSlots J9R14LowPrecisionComplete
open J9R14LowPrecisionTiedCube

noncomputable section
variable {S R Q A : Type*} [LinearOrder S] [Fintype R] [Fintype Q]
variable {a b : ℕ} [Fintype (Page a b S)]
variable (ρ : R→Physical a b S) (κ : Q→Physical a b S)
variable (old : Finset A) (owner : Slot (Page a b S) (2^a)→A) {t : ℤ}
local notation "D" => nativeSeats ρ κ
local notation "PROT" => protectedOwner D old owner t

theorem old_ports_supply (hPorts : ∀ u∈old, ∃ q : Q, owner (κ q)=u)
    (u : FreeOwner D old owner t) : ∃ q, PROT q=some u := by
  have hOld : u.val∈old := (Finset.mem_sdiff.mp u.2).1
  obtain ⟨q,hq⟩ := hPorts u.val hOld
  refine ⟨q,?_⟩
  have h : owner ((nativeSeats ρ κ).col q)∈kept D old owner t := hq ▸ u.2
  rw [protectedOwner,dif_pos h]
  congr 1
  exact Subtype.ext hq

variable (mask : MaskFamily a b S) (i : Fin a) (p : ℕ)
variable [Fintype (Mode i p mask)]
local notation "W" => Mode i p mask

def legalTicket (β : W→₀ℕ) : Finset ((R→Bool) × (R→Option W)) :=
  Finset.univ.filter fun c => (∑ r : R, LiteralPortCompiler.exponent (c.2 r))=β

omit [Fintype (Page a b S)] in
theorem legal_exact (β : W→₀ ℕ) (c : (R→Bool)×(R→Option W)) :
    c∈legalTicket mask i p β ↔ (∑ r : R, LiteralPortCompiler.exponent (c.2 r))=β := by
  simp [legalTicket]

variable (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable {K : Type*} [CommRing K] (hnil : (2:K)^p=0)

/-- All projected slots at any integral probe when p <= the actual
untouched equality count. The same theorem permits the empty mode,
any legal repeated mode, and any sign word in the remaining tables. -/
theorem complete_menu_zero (z : K)
    (weight : (R→Bool)→(Rest PROT→Bool)→TwoLocal)
    (hPorts : ∀ u∈old, ∃ q : Q, owner (κ q)=u)
    (hp : p≤(kept D old owner t).card) :
    ∀ β : W→₀ℕ,
      slot ρ κ mask i ht hv p old owner hnil z (legalTicket mask i p β)
        Prod.fst Prod.snd (fun c => weight c.1)=0 := by
  intro β
  exact native_slot_zero ρ κ mask i ht hv p old owner hnil z _
    Prod.fst Prod.snd (fun c => weight c.1) β (fun c hc => (legal_exact mask i p β c).mp hc)
    (old_ports_supply ρ κ old owner (t:=t) hPorts) hp

theorem four_clone_outer_menu (z : K)
    (weight : (R→Bool)→(Rest PROT→Bool)→TwoLocal)
    (hPorts : ∀ u∈old, ∃ q : Q, owner (κ q)=u) (N : ℕ)
    (hOuter : t=((2^a:ℕ):ℤ)-1) (hOld : old.card=4*N)
    (hPack : Fintype.card (Page a b S) * 2^a ≤ 3*(24*N))
    (hp : (p:ℚ) ≤ (24*(N:ℚ))/6-3*(24*(N:ℚ))/(2^a:ℕ)) :
    ∀ β : W→₀ℕ,
      slot ρ κ mask i ht hv p old owner hnil z (legalTicket mask i p β)
        Prod.fst Prod.snd (fun c => weight c.1)=0 := by
  intro β
  exact four_clone_outer_slot_zero ρ κ mask i ht hv p old owner hnil z _
    Prod.fst Prod.snd (fun c => weight c.1) β (fun c hc => (legal_exact mask i p β c).mp hc)
    (old_ports_supply ρ κ old owner (t:=t) hPorts) N hOuter hOld hPack hp

#print axioms old_ports_supply
#print axioms legal_exact
#print axioms complete_menu_zero
#print axioms four_clone_outer_menu

end
end J9R14LowPrecisionMenu
