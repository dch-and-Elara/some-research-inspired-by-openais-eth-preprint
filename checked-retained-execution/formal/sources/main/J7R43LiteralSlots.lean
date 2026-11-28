import J6R11IntegralStep
import J6R14ZeroModeAlgebra

/-! Literal J7 observations are individual physical children, not the
product over all groups at a fixed tuple. The algebra here tracks the
single source factor at its actual source packet. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral J6R11Integral
  J6R9PacketScopes J6R9PacketChild J6R10PacketAssembly J6R10RowAffine J6R10RowIdentity
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

section Packets
variable {R G K M I : Type*} [CommRing R] [DecidableEq G] [DecidableEq K]
  [Fintype M] [DecidableEq M]

/-- A singleton exponent contributes a moment in exactly its source packet.
It takes the constant row coefficient in every packet of that source group,
with no numerical-zero assumption on the probe. -/
theorem source_packet_singleton (target source : M → G × K) (m : M)
    (hsep : (target m).1 ≠ (source m).1) (k : K)
    (ports : Finset I) (bit : I → Bool) (base : I → R)
    (cross : I → M → R) (moment : M → R) :
    J6RecursiveModes.packet target source (source m).1 k ports bit base cross moment
      (Finsupp.single m 1) =
    (∏ r ∈ ports, LiteralPortCompiler.affine (bit r) (base r)) *
      (if k=(source m).2 then moment m else 1) := by
  have hfilter : ((Finsupp.single m 1 : M →₀ ℕ).filter
      (fun j => target j=((source m).1,k)))=0 := by
    ext j
    by_cases hj : j=m
    · subst j
      have hn : target m ≠ ((source m).1,k) := by
        intro h
        have he := congrArg (fun x : G × K => x.1) h
        exact hsep he
      simp [hn]
    · rw [Finsupp.filter_apply]
      split <;> simp [Finsupp.single_eq_of_ne hj]
  rw [J6RecursiveModes.packet,hfilter,← MvPolynomial.constantCoeff_eq,map_prod]
  simp only [J6R14ZeroMode.row_constant]
  congr 1
  by_cases hk : k=(source m).2
  · subst k
    rw [if_pos rfl, Finset.prod_eq_single m]
    · simp
    · intro j _ hj
      simp [Finsupp.single_eq_of_ne hj]
    · intro hm
      exact (hm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Prod.eta _⟩)).elim
  · rw [if_neg hk]
    apply Finset.prod_eq_one
    intro j hj
    have jne : j ≠ m := by
      rintro rfl
      exact hk ((congrArg Prod.snd (Finset.mem_filter.mp hj).2).symm)
    simp [Finsupp.single_eq_of_ne jne]
end Packets

section Actual
variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
variable (p : ℕ) (z : Box f ell p) (old : EntryFile f ell N) (hf : f.Monic)

def actualBaselineWeight (g : G) (v : PhysicalState P i g) : Box f ell p :=
  oldState P i g p old hf v * ∏ k, ∏ r ∈ actualRows (childBlock P i) g k,
    LiteralPortCompiler.affine
      (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v r)
      (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p
        (box_two_nil p f ell) z g v r)

theorem literal_baseline_child (ht : t≠0) (hv : padicValInt 2 t=i.val) (g : G) :
    reduce p f ell (actualChildTruth P i ht hv p z old hf 0 g) =
      ∑ v : PhysicalState P i g, actualBaselineWeight P i (t:=t) p z old hf g v := by
  rw [actualChildTruth,actual_physical_child]
  simp only [actualBaselineWeight,actualPacket,J6R14ZeroMode.packet_constant]

/-- The subgroup of the physical mode source, alone, has exactly its
baseline weighting times the moment. This is the observable in J7. -/
theorem literal_singleton_child (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (m : Mode i p P.mask) :
    reduce p f ell (actualChildTruth P i ht hv p z old hf (Finsupp.single m 1)
      (source P.mask i m)) =
      ∑ v : PhysicalState P i (source P.mask i m),
        actualBaselineWeight P i (t:=t) p z old hf (source P.mask i m) v *
          stateMoment P i (source P.mask i m) p v m := by
  rw [actualChildTruth,actual_physical_child]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have hs : (childTarget P i m).1 ≠ (childSource P i m).1 :=
    source_distinct P.mask i m
  have hpacket (k : Page a P.copies G) :
      actualPacket P i ht hv p (box_two_nil p f ell) z (Finsupp.single m 1)
        (source P.mask i m) k v =
      (∏ r ∈ actualRows (childBlock P i) (source P.mask i m) k,
        LiteralPortCompiler.affine
          (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i (source P.mask i m) v r)
          (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p
            (box_two_nil p f ell) z (source P.mask i m) v r)) *
          (if k=(childSource P i m).2 then stateMoment P i (source P.mask i m) p v m else 1) := by
    unfold actualPacket
    have h := source_packet_singleton (R:=Box f ell p) (I:=E) (childTarget P i)
      (childSource P i) m hs k (actualRows (childBlock P i) (source P.mask i m) k)
      (groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i (source P.mask i m) v)
      (groupBase (fun e => P.seat e) (fun e => P.seat e) P.mask i t p
        (box_two_nil p f ell) z (source P.mask i m) v)
      (fun r m => scaledRow P.mask i ht hv p (box_two_nil p f ell) z (P.seat r) m)
      (stateMoment P i (source P.mask i m) p v)
    by_cases hk : k=(childSource P i m).2
    · simpa only [if_pos hk] using h
    · simpa only [if_neg hk] using h
  simp only [actualBaselineWeight,hpacket, Finset.prod_mul_distrib, mul_assoc]
  congr 2
  rw [Finset.prod_eq_single (childSource P i m).2]
  · rw [if_pos rfl]
  · intro k _ hk
    rw [if_neg hk]
  · intro hk
    exact (hk (Finset.mem_univ _)).elim
end Actual

#print axioms source_packet_singleton
#print axioms literal_baseline_child
#print axioms literal_singleton_child
end
end J7R43Literal