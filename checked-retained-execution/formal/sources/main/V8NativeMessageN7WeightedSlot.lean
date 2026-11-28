import V8NativeMessageN7Kernel
import V8NativeMessageN7Weighted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

/-! The actual weighted whole-product bound. Every exponent is charged
at its unique target packet, while arbitrary source moments remain in
the allowed integral receiving ring. -/
namespace V8NativeMessage.N7
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open J6R9PacketChild J6R10PacketAssembly J6R10RowIdentity

noncomputable section
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

abbrev nativeModeCost (P : PhysicalPacking N a G) (i : Fin a) (p : ℕ)
    (β : Mode i p P.mask →₀ ℕ) : ℕ :=
  modeCost (fun m=>a+1-i.val+m.order.val) β

theorem actual_whole_slot_weight (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (h₂ : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (file : EntryFile f ell N) (hf : f.Monic) (β : Mode i p P.mask→₀ℕ) :
    (2:Residue f ell p)^nativeModeCost P i p β ∣ V8PooledMenu.slot P i ht hv p h₂ z file hf β := by
  classical
  let w (m : Mode i p P.mask) := a+1-i.val+m.order.val
  have H := V8PooledMenu.projected_slot P i ht hv p h₂ z file hf β (RingHom.id _)
  simp only [RingHom.id_apply] at H
  rw [H]
  change (2:Residue f ell p)^modeCost w β ∣ _
  rw [← modeCost_partition w (childTarget P i) β,← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_dvd_prod_of_dvd
  intro g _
  apply Finset.dvd_sum
  intro v _
  apply Dvd.dvd.trans _ (dvd_mul_left _ _)
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_dvd_prod_of_dvd
  intro k _
  unfold actualPacket
  apply gain_packet
  intro r _ m
  exact native_cross_weight_gain P.mask i ht hv p h₂ z (P.seat r) m

theorem projected_whole_slot_weight {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (h₂ : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (file : EntryFile f ell N) (hf : f.Monic) (β : Mode i p P.mask→₀ℕ)
    (ψ : Residue f ell p →+* S) {q : ℕ} (hq : q≤nativeModeCost P i p β) (nil : (2:S)^q=0) :
    ψ (V8PooledMenu.slot P i ht hv p h₂ z file hf β)=0 := by
  obtain ⟨v,hv⟩ := (pow_dvd_pow (2:Residue f ell p) hq).trans
    (actual_whole_slot_weight P i ht hv p h₂ z file hf β)
  rw [hv,map_mul,map_pow,map_ofNat,nil,zero_mul]

#print axioms actual_whole_slot_weight
#print axioms projected_whole_slot_weight
end
end V8NativeMessage.N7
