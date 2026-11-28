import J6R12BlueprintPacketReceipt
import J6RecursiveMenu
import JointContraction

/-! The same printed child at zeta=0: positive target exponent
erases the child, while a source-only tuple multiplies the actual
uncrossed affine row factors by the true source moment powers. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking DenominatorBudget J6R10Repack J6R11Blueprint J6R9Recursive
open J6R9PacketScopes J6R9PacketChild J6R9PacketCoeff J6R9PacketLocal
open J6R10RowIdentity J6R10RowAffine J6R10PacketAssembly

noncomputable section
variable {a : ℕ}

theorem literal_W_zero {R : Type*} [CommRing R] (p : ℕ) (hnil : (2:R)^p=0)
    (t k : ℤ) :
    (W a t k).eval₂ (J6ZeroTransport.reduceAt p hnil) 0 =
      if k=t then J6ZeroTransport.reduceAt p hnil (rho a t) else 0 := by
  let φ := J6ZeroTransport.reduceAt p hnil
  let H := Polynomial.eval₂RingHom φ 0
  change H (W a t k) = _
  by_cases e : k=t
  · rw [W,if_pos e,if_pos e,cHat,map_mul,map_prod]
    simp [H,φ]
  · rw [W,if_neg e,if_neg e]
    simp [H]

theorem literal_scaled_zero {G R : Type*} [LinearOrder G] [CommRing R] {b : ℕ}
    (mask : MaskFamily a b G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0)
    (w : Physical a b G) (m : Mode i p mask) :
    scaledRow mask i ht hv p hnil 0 w m=0 := by
  by_cases h : rowBlock mask i w=target mask i m
  · simp [scaledRow,crossNorm,h,J6R9PacketScaled.normalized]
  · simp [scaledRow,crossNorm,h]

section Source
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a)
variable {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (p : ℕ) (hnil : (2:Residue f ell p)^p=0)
variable (old : EntryFile f ell N) (hf : f.Monic)

abbrev ModeTuple := Mode i p P.mask →₀ ℕ

abbrev LegalTuple :=
  ↥(J6RecursiveMenu.menu p (J6R10RowAffine.weight i p P.mask))

variable (β : ModeTuple P i p) (g : G)

def HasNoTarget : Prop :=
  ∀ m : Mode i p P.mask, (target P.mask i m).2=g → β m=0

omit [Fintype E] [Fintype A] [Fintype B] in
theorem legal_exponent_small (β₀ : LegalTuple P i p) (m : Mode i p P.mask) : β₀.val m<p := by
  have h := (J6RecursiveMenu.exact_printed_menu p (J6R10RowAffine.weight i p P.mask)
      (fun j=>Nat.zero_lt_succ j.order.val) β₀.val).mp β₀.prop
  exact (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ m.order.val)).trans_lt <|
    (Finset.single_le_sum (fun j _=>Nat.zero_le (J6R10RowAffine.weight i p P.mask j*β₀.val j))
     (Finset.mem_univ m)).trans_lt h

def physicalReply : Residue f ell p :=
  reduce p f ell ((actualPacketHost P i ht hv p hnil 0 old β g).contract hf)

def packetRows (k : Page a P.copies G) (v : PhysicalState P i g) : Residue f ell p :=
  ∏ e ∈ actualRows (childBlock P i) g k,
    LiteralPortCompiler.affine (groupBit (fun q=>P.seat q) (fun q=>P.seat q) P.mask i g v e)
      (groupBase (fun q=>P.seat q) (fun q=>P.seat q) P.mask i t p hnil 0 g v e)

def packetMoments (k : Page a P.copies G) (v : PhysicalState P i g) : Residue f ell p :=
  ∏ m ∈ Finset.univ.filter (fun m : Mode i p P.mask=>childSource P i m=(g,k)),
    (stateMoment (R:=Residue f ell p) P i g p v m)^β m

omit [Fintype A] [Fintype B] in
theorem source_only_packet (hh : HasNoTarget P i p β g)
    (k : Page a P.copies G) (v : PhysicalState P i g) :
    actualPacket P i ht hv p hnil 0 β g k v =
      packetRows (t:=t) P i p hnil g k v * packetMoments P i p β g k v := by
  have hz : β.filter (fun m=>childTarget P i m=(g,k))=0 := by
    ext m
    by_cases h : childTarget P i m=(g,k)
    · rw [Finsupp.filter_apply,if_pos h,Finsupp.zero_apply]
      exact hh m (congrArg Prod.fst h)
    · rw [Finsupp.filter_apply,if_neg h,Finsupp.zero_apply]
  unfold actualPacket J6RecursiveModes.packet packetRows packetMoments
  simp only [literal_scaled_zero,J6RecursiveModes.row_zero,hz,←map_prod,MvPolynomial.coeff_C]
  simp

omit [Fintype A] [Fintype B] in
theorem positive_target_packet_zero
    (k : Page a P.copies G) (v : PhysicalState P i g)
    (b : Mode i p P.mask) (whereb : childTarget P i b=(g,k)) (pos : β b≠0) :
    actualPacket P i ht hv p hnil 0 β g k v=0 := by
  unfold actualPacket
  simp only [literal_scaled_zero]
  apply J6RecursiveModes.packet_positive_target_zero
  intro eq
  have h := DFunLike.congr_fun eq b
  rw [Finsupp.filter_apply,if_pos whereb,Finsupp.zero_apply] at h
  exact pos h

theorem actual_positive_target_child_zero
    (b : Mode i p P.mask) (loc : (target P.mask i b).2=g) (pos : β b≠0) :
    physicalReply P i ht hv p hnil old hf β g=0 := by
  unfold physicalReply
  rw [actualPacketHost_receive]
  refine Finset.sum_eq_zero fun v _=>?_ 
  have h : childTarget P i b=(g,b.page) := Prod.ext loc rfl
  rw [Finset.prod_eq_zero (Finset.mem_univ b.page)
    (positive_target_packet_zero P i ht hv p hnil β g b.page v b h pos),mul_zero]

theorem actual_source_only_child
    (β₀ : LegalTuple P i p) (hh : HasNoTarget P i p β₀.val g) :
    physicalReply P i ht hv p hnil old hf β₀.val g =
      ∑ v : PhysicalState P i g, oldState P i g p old hf v *
        ((∏ k, packetRows (t:=t) P i p hnil g k v) *
          ∏ k,packetMoments P i p β₀.val g k v) := by
  unfold physicalReply
  rw [actualPacketHost_receive]
  simp_rw [source_only_packet P i ht hv p hnil β₀.val g hh,Finset.prod_mul_distrib]

end Source

theorem parity_features_not_full_precision : ((2 : ZMod 4)^2) ≠ 2 := by decide

#print axioms literal_W_zero
#print axioms literal_scaled_zero
#print axioms legal_exponent_small
#print axioms source_only_packet
#print axioms positive_target_packet_zero
#print axioms actual_positive_target_child_zero
#print axioms actual_source_only_child
#print axioms parity_features_not_full_precision
end
end J5R41LiteralChildCost