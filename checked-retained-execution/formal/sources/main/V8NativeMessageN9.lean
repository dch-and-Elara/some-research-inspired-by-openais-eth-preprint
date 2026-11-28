import V8NativeMessageChildMenu

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
set_option maxRecDepth 4000

namespace V8NativeMessage
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open V8PooledMenu J6R10Integral
noncomputable section

section Cardinality
variable {E A B G : Type} [Fintype E] [LinearOrder G] [Fintype G]
  {a : ℕ} {N : Network E A B}

def childBits (P : PhysicalPacking N a G) (i : Fin a) : ℕ :=
  Fintype.card G + Fintype.card (TileForm P i)

omit [Fintype E] in
theorem form_card (P : PhysicalPacking N a G) (i : Fin a) :
    Fintype.card (TileForm P i) = Fintype.card (Page a P.copies G) * (2^(i.val+1)*2) := by
  simp [TileForm]

omit [Fintype E] in
theorem childTape_card (P : PhysicalPacking N a G) (i : Fin a) :
    Fintype.card (ChildTape P i) = 2^childBits P i := by
  simp [ChildTape,childBits,pow_add]

/-- Two forms per possible padded tile. The actual labelled packing has
at most three times the real wire count many padded seats. -/
theorem forms_budget (P : PhysicalPacking N a G) (i : Fin a) :
    Fintype.card (TileForm P i) ≤ (12 * Fintype.card E) / (2^a / 2^i.val) := by
  rw [dyadic_div_pow i.isLt.le]
  apply (Nat.le_div_iff_mul_le (by positivity : 0<2^(a-i.val))).mpr
  rw [form_card]
  have hslots := total_slots P.mask
  rw [Nat.card_eq_fintype_card (α:=Page a P.copies G)] at hslots
  calc
    _ = Fintype.card (Page a P.copies G) * (2^(a-i.val)*2^(i.val+1))*2 := by ac_rfl
    _ = 4*(Fintype.card (Page a P.copies G)*2^a) := by
      rw [← pow_add,show a-i.val+(i.val+1)=a+1 by omega,pow_succ]
      ring
    _ ≤ 12*Fintype.card E := by
      have h := P.paddedBudget
      rw [← hslots,Nat.card_eq_fintype_card] at h
      omega

theorem childBits_le (P : PhysicalPacking N a G) (i : Fin a) :
    childBits P i ≤ Fintype.card G + (12 * Fintype.card E) / (2^a / 2^i.val) := by
  exact Nat.add_le_add_left (forms_budget P i) _

end Cardinality

namespace Five
open V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin
variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}

def parityPrecision (V : Type) [Fintype V] : PublicPrecision V where
  prec := fun _ => 1
  positive := fun _ => Nat.zero_lt_one
  cap i := by have h := i.isLt; unfold rootA; omega

def ChildAddress (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) :=
  {q : Address P hu huM t × Fin 64 //
    RestrictedChild P (rootIndex hu huM t) q.1.beta q.2}

def actualChildMenu (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V → Bool) :
    ChildAddress P hu huM t → Residue f 1 1 :=
  fun q =>
    projectedChild P (rootIndex hu huM t) (nonzero_site hu huM t) (rootIndex_val hu huM t)
      (high t) (box_two_nil (high t) f 1)
      (readProbe f (high t) (probes.word t q.val.1.probeIdx)) (file f G p s) hf q.val.1.beta q.val.2
      (observe f (high t) 1 (precision_fits hu huM (parityPrecision V) t))

theorem parityBox (f : ℤ[X]) : (2:Residue f 1 1)=0 := by
  simpa only [pow_one] using box_two_nil 1 f 1

def decodeNativeChildren (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (tape : ChildTape P (rootIndex hu huM t)) :
    ChildAddress P hu huM t → Residue f 1 1 :=
  fun q => decodeChild P (rootIndex hu huM t) q.val.1.beta q.val.2 tape (parityBox f)

theorem N9_native (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree) (s : V → Bool) :
    actualChildMenu P hu huM t probes hf s =
      decodeNativeChildren (f:=f) P hu huM t
        (encodeChildren P (rootIndex hu huM t) t.val (flags G p s)) := by
  funext q
  exact N9_projected_child P (rootIndex hu huM t)
    (nonzero_site hu huM t) (rootIndex_val hu huM t) (high t) (box_two_nil (high t) f 1)
    _ (rootPrec V) (rootPrec_pos V) hf hd (flags G p s) q.val.1.beta q.val.2 _ (parityBox f) q.property

theorem N9_tape_budget (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V) :
    childBits P (rootIndex hu huM t) ≤
      64 + (12*wireSize V) / (2^rootA V / 2^(level hu huM t).val) := by
  simpa only [Fintype.card_fin,← (root_sizes V G p).1] using childBits_le P (rootIndex hu huM t)

#print axioms form_card
#print axioms childTape_card
#print axioms forms_budget
#print axioms childBits_le
#print axioms N9_native
#print axioms N9_tape_budget

end Five
end
end V8NativeMessage