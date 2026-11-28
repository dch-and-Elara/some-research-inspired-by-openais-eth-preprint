import V8PooledMenuPolynomial

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

/-! The N7 signed-grid coefficients in the actual packet compiler, plus
the whole-slot consequences before any particular graph is installed.
The new b-dependent gain is stronger than the simple uniform projection. -/
namespace V8NativeMessage.N7
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes J6R9PacketLocal
open J6R9PacketCoeff J6R9PacketChild J6R10RowAffine J6R10RowIdentity J6R10PacketAssembly

section Cross
variable {G R : Type*} [LinearOrder G] [CommRing R] {a b : ℕ}

theorem native_cross_weight_gain (mask : MaskFamily a b G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (h₂ : (2:R)^p=0) (z : R) (w : Physical a b G)
    (m : Mode i p mask) :
    (2:R)^(a+1-i.val+m.order.val) ∣ scaledRow mask i ht hv p h₂ z w m := by
  classical
  by_cases h : rowBlock mask i w = target mask i m
  · let d := crossingOf ht hv (targeted_row_bit mask i w m h)
    unfold scaledRow
    rw [on_target_exact mask i ht hv p h₂ z w m h]
    change (2:R)^(a+1-i.val+m.order.val) ∣
      J6R9PacketReceive.mode a p h₂ i.isLt.le d z m.order.val
    have hl : (2:R)^(a+1-i.val) ∣ J6R9PacketReceive.leading a p h₂ i.isLt.le d z := by
      unfold J6R9PacketReceive.leading
      apply (pow_dvd_pow (2:R) (Nat.sub_le_sub_left d.level_le _) ).trans
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    have hratio : (2:R) ∣ J6R9PacketReceive.ratio a p h₂ i.isLt.le d z := by
      unfold J6R9PacketReceive.ratio
      have hr : (1 : ℕ) ≤ (i.val + 1) - d.level := by
        have hm := d.level_le
        omega
      have hc := (pow_dvd_pow (2:R) hr).trans
        (dvd_mul_right ((2:R)^(i.val+1-d.level)) (J6R9PacketReceive.inverseB a p h₂ i.isLt.le d z))
      simpa only [pow_one] using hc
    rw [pow_add,J6R9PacketReceive.mode]
    exact mul_dvd_mul hl (pow_dvd_pow_of_dvd hratio m.order.val)
  · rw [scaledRow,off_target mask i ht hv p h₂ z w m h,mul_zero]
    exact dvd_zero _

theorem native_cross_zero_at_zero (mask : MaskFamily a b G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (h₂ : (2:R)^p=0) (w : Physical a b G) (m : Mode i p mask) :
    scaledRow mask i ht hv p h₂ 0 w m = 0 := by
  classical
  by_cases h : rowBlock mask i w = target mask i m
  · unfold scaledRow
    rw [on_target_exact mask i ht hv p h₂ 0 w m h]
    simp [J6R9PacketReceive.mode,J6R9PacketReceive.leading]
  · rw [scaledRow,off_target mask i ht hv p h₂ 0 w m h,mul_zero]

end Cross

section Slot
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

theorem target_zero_kills_whole {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (h₂ : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (hβ : β≠0) (ψ : Residue f ell p →+* S)
    (noCross : ∀ (r : E) (m : Mode i p P.mask),ψ (scaledRow P.mask i ht hv p h₂ z (P.seat r) m)=0) :
    ψ (V8PooledMenu.slot P i ht hv p h₂ z file hf β)=0 := by
  classical
  obtain ⟨m,hm⟩ : ∃ m, β m≠0 := by
    by_contra! hz
    exact hβ (Finsupp.ext fun m => hz m)
  let g := (childTarget P i m).1
  let k := (childTarget P i m).2
  have htarget : childTarget P i m = (g,k) := (Prod.eta _).symm
  have hfilter : β.filter (fun m' => childTarget P i m' = (g,k)) ≠ 0 := by
    intro hb
    have h := congrArg (fun w : Mode i p P.mask →₀ ℕ => w m) hb
    exact hm (by simpa only [Finsupp.filter_apply,htarget,if_pos rfl,Finsupp.zero_apply] using h)
  rw [V8PooledMenu.projected_slot]
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  apply Finset.sum_eq_zero
  intro v _
  have hz : (fun (r : E) (m : Mode i p P.mask) => ψ (scaledRow P.mask i ht hv p h₂ z (P.seat r) m)) =
      fun _ _ => 0 := funext fun r => funext (noCross r)
  have hp : ψ (actualPacket P i ht hv p h₂ z β g k v)=0 := by
    rw [actualPacket,V8PooledMenu.packet_map,hz]
    exact J6RecursiveModes.packet_positive_target_zero _ _ _ _ _ _ _ _ _ hfilter
  rw [Finset.prod_eq_zero (Finset.mem_univ k) hp,mul_zero]

theorem native_zero_probe_nonzero_mode
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (h₂ : (2:Residue f ell p)^p=0) (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (hβ : β≠0) :
    V8PooledMenu.slot P i ht hv p h₂ 0 file hf β=0 := by
  exact target_zero_kills_whole P i ht hv p h₂ 0 file hf β hβ (RingHom.id _) <|
    fun r m => native_cross_zero_at_zero P.mask i ht hv p h₂ (P.seat r) m

theorem zero_mode_same_probe_mod_two {S : Type*} [CommRing S]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0)
    (file : EntryFile f 1 N) (hf : f.Monic) (z z' : Residue f 1 p)
    (ψ : Residue f 1 p →+* S) (hTwo : (2:S)=0) :
    ψ (V8PooledMenu.slot P i ht hv p h₂ z file hf 0)=
      ψ (V8PooledMenu.slot P i ht hv p h₂ z' file hf 0) := by
  rw [V8PooledMenu.projected_zero_slot,V8PooledMenu.projected_zero_slot]
  unfold V8PooledMenu.zeroValue
  refine Finset.prod_congr rfl fun g _ => ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  apply congrArg (ψ (oldState P i g p file hf v)*·)
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Finset.prod_congr rfl fun r _ => ?_
  apply congrArg (LiteralPortCompiler.affine _)
  rw [← V8PooledMenu.baseScaled_eval P i t g v r p h₂ z ψ,
    ← V8PooledMenu.baseScaled_eval P i t g v r p h₂ z' ψ,hTwo,zero_mul,zero_mul]

end Slot

#print axioms native_cross_weight_gain
#print axioms native_cross_zero_at_zero
#print axioms target_zero_kills_whole
#print axioms native_zero_probe_nonzero_mode
#print axioms zero_mode_same_probe_mod_two

end V8NativeMessage.N7
