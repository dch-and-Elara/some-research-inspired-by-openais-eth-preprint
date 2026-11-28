import V8PooledMenuKernel
import J6R12BlueprintPacketReceipt
import J6R14ZeroModeAlgebra

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2700000

namespace V8PooledMenu
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open J6R10PacketAssembly J6R10RowAffine J6R10RowIdentity
open J6R11Blueprint

section RingMaps
variable {R S : Type*} [CommRing R] [CommRing S]

theorem affine_map (ψ : R →+* S) (b : Bool) (x : R) :
    ψ (LiteralPortCompiler.affine b x) = LiteralPortCompiler.affine b (ψ x) := by
  cases b <;> simp [LiteralPortCompiler.affine]

theorem slope_map (ψ : R →+* S) (b : Bool) :
    ψ (LiteralPortCompiler.slope (R:=R) b) = LiteralPortCompiler.slope (R:=S) b := by
  cases b <;> simp [LiteralPortCompiler.slope]

theorem row_map {M : Type*} [Fintype M] [DecidableEq M]
    (ψ : R →+* S) (b : Bool) (val : R) (cross : M → R) :
    MvPolynomial.map ψ (J6RecursiveModes.row b val cross) =
      J6RecursiveModes.row b (ψ val) (fun m => ψ (cross m)) := by
  simp only [J6RecursiveModes.row, map_add, map_sum, MvPolynomial.map_C, MvPolynomial.map_monomial,
    map_mul,affine_map,slope_map]

theorem packet_map {G K M P : Type*} [DecidableEq G] [DecidableEq K]
    [Fintype M] [DecidableEq M]
    (ψ : R →+* S) (target source : M → G × K) (g : G) (k : K)
    (ports : Finset P) (bit : P → Bool) (base : P → R) (cross : P → M → R)
    (moment : M → R) (β : M →₀ ℕ) :
    ψ (J6RecursiveModes.packet target source g k ports bit base cross moment β) =
      J6RecursiveModes.packet target source g k ports bit (fun r => ψ (base r))
        (fun r m => ψ (cross r m)) (fun m => ψ (moment m)) β := by
  unfold J6RecursiveModes.packet
  rw [map_mul, ← MvPolynomial.coeff_map]
  simp only [map_prod,map_pow,row_map]

end RingMaps

section Actual
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

noncomputable def slot (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (h₂ : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) : Residue f ell p :=
  ∏ g : G, reduce p f ell ((actualPacketHost P i ht hv p h₂ z file β g).contract hf)

/-- This projects the existing completed slot, not a new low-precision
menu. All mode, placement and probe coordinates are high-precision ones. -/
theorem projected_slot {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (h₂ : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (ψ : Residue f ell p →+* S) :
    ψ (slot P i ht hv p h₂ z file hf β) =
      ∏ g : G, ∑ v : PhysicalState P i g,
        ψ (oldState P i g p file hf v) *
        ∏ k, ψ (actualPacket P i ht hv p h₂ z β g k v) := by
  rw [slot,map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [actualPacketHost_receive P i ht hv p h₂ z file β g hf,map_sum]
  exact Finset.sum_congr rfl (fun _ _ => by rw [map_mul,map_prod])

noncomputable def zeroValue {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ) (h₂ : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (file : EntryFile f ell N) (hf : f.Monic)
    (ψ : Residue f ell p →+* S) : S :=
  ∏ g : G, ∑ v : PhysicalState P i g,
    ψ (oldState P i g p file hf v) *
      ∏ k, ∏ r ∈ actualRows (childBlock P i) g k,
        LiteralPortCompiler.affine
          (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v r)
          (ψ (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p h₂ z g v r))

theorem projected_zero_slot {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (h₂ : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (file : EntryFile f ell N) (hf : f.Monic)
    (ψ : Residue f ell p →+* S) :
    ψ (slot P i ht hv p h₂ z file hf 0) = zeroValue P i t p h₂ z file hf ψ := by
  rw [projected_slot,zeroValue]
  refine Finset.prod_congr rfl fun g _ => ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  apply congrArg (ψ (oldState P i g p file hf v)*·)
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [actualPacket,packet_map, J6R14ZeroMode.packet_constant]

/-- It is the complete product that vanishes. We exhibit one target child,
not a universal erasure statement about individual source-only children. -/
theorem projected_nonzero_slot {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (h₂ : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (hβ : β≠0) (ψ : Residue f ell p →+* S)
    {q : ℕ} (hq : q ≤ a+1-i.val) (hzero : (2:S)^q=0) :
    ψ (slot P i ht hv p h₂ z file hf β) = 0 := by
  classical
  obtain ⟨m,hm⟩ : ∃ m, β m ≠ 0 := by
    by_contra! h
    apply hβ
    ext m
    exact h m
  let g := (childTarget P i m).1
  let k := (childTarget P i m).2
  have htarget : childTarget P i m = (g,k) := (Prod.eta _).symm
  have hfilter : β.filter (fun m' => childTarget P i m' = (g,k)) ≠ 0 := by
    intro hb
    have h := congrArg (fun w : Mode i p P.mask →₀ ℕ => w m) hb
    exact hm (by simpa [htarget] using h)
  rw [projected_slot]
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  apply Finset.sum_eq_zero
  intro v _
  have hpacket : ψ (actualPacket P i ht hv p h₂ z β g k v)=0 := by
    rw [actualPacket,packet_map]
    have hz : (fun (r : E) (m' : Mode i p P.mask) =>
        ψ (scaledRow P.mask i ht hv p h₂ z (P.seat r) m')) = fun _ _ => 0 := by
      funext r m'
      exact project_cross_zero ψ P.mask i ht hv p h₂ z (P.seat r) m' hq hzero
    rw [hz]
    exact J6RecursiveModes.packet_positive_target_zero _ _ _ _ _ _ _ _ _ hfilter
  rw [Finset.prod_eq_zero (Finset.mem_univ k) hpacket, mul_zero]

#print axioms affine_map
#print axioms row_map
#print axioms packet_map
#print axioms slot
#print axioms projected_slot
#print axioms projected_zero_slot
#print axioms projected_nonzero_slot

end Actual
end V8PooledMenu
