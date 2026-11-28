import J6R18ChildWritePhysical
import J6R18ChildWriteRun
import Mathlib.Algebra.MvPolynomial.Rename

/-! The mode ordinal order and row enumeration do not change the
coefficient: exactly the actual physical packet polynomial is read. -/
namespace J6R18ChildWrite
open scoped BigOperators Classical Polynomial
open MvPolynomial J6PacketCoefficientBridge
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates AOracleWitness
open A1R10 A1R11 A1R12
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketChild
open J6R10Repack J6R10RowAffine J6R10RowIdentity

theorem typedRow_poly {p ell a q m : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a)
    (i : Fin a) (b : ℕ) (cols : List (SlotBit a)) (ms : Fin m→ModeInput a p i q)
    (hc : ∀ j,(ms j).code=encodeBits b j.succ.val) (r : SlotBit a) :
    let hnil := AOracleSuccinctPhysical.double_quotient_two_nilpotent (Modulus p hp fw) ell
    rowPoly ((typedRowWords hp he hv z t i cols ms r).map (termMeaning hp)) =
      J6RecursiveModes.row r.assigned (localMeaning p hnil t (uvRead hp fw ell z) r cols)
        (fun j=>crossMeaning t (uvRead hp fw ell z) r (ms j)) := by
  let R := Truncated (Modulus p hp fw) ell
  let L := localSum hp he hv z t r cols
  let B := baseFactor hp he hv r.assigned L
  let K (j : Fin m) := (variableTerm hp he hv z t i r (ms j)).result.value
  have hB := (baseFactor_exact hp he hv r.assigned L).1
  rw [(localSum_exact hp he hv z t ht r cols).1] at hB
  have hk (j : Fin m) : uvRead hp fw ell (K j) =
      LiteralPortCompiler.slope r.assigned*crossMeaning t (uvRead hp fw ell z) r (ms j) :=
    (variableTerm_exact hp he hv z t ht i r (ms j) b (by rw [hc,encodeBits_length])).2.1
  unfold typedRowWords rowPoly J6RecursiveModes.row
  simp only [List.map_cons,List.sum_cons,List.map_map,Function.comp_def,termMeaning,choice_zero,
    exponent,Option.elim'_none,monomial_zero']
  rw [show uvRead hp fw ell B.result=_ from hB]
  congr 1
  simp only [choice_succ,Option.elim'_some]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (monomial (Finsupp.single j 1)) (hk j)

theorem rename_signed_row {R A B : Type*} [CommRing R] [Fintype A] [Fintype B] (ξ : A≃B)
    (y : Bool) (base : R) (C₁ : A→R) (C₂ : B→R) (h : ∀ j,C₁ j=C₂ (ξ j)) :
    rename ξ (J6RecursiveModes.row y base C₁)=J6RecursiveModes.row y base C₂ := by
  unfold J6RecursiveModes.row
  rw [map_add,rename_C,map_sum]
  congr 1
  apply Fintype.sum_equiv ξ
  intro j
  rw [rename_monomial,Finsupp.mapDomain_single,h]

variable {E A B G : Type} [Fintype E] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

structure ModeMeaning (P : PhysicalPacking N a G) (i : Fin a)
    (g : G) (k : Page a P.copies G) {p q m : ℕ}
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ) (ms : Fin m→ModeInput a p i q) : Prop where
  tile : ∀ j,(ms j).tile.val=(ξ j).tile.val
  order : ∀ j,(ms j).order=(ξ j).order
  target : ∀ j,(ms j).targeted=true ↔ childTarget P i (ξ j)=(g,k)
  source : ∀ j,(ms j).sourced=true ↔ childSource P i (ξ j)=(g,k)
  exponents : ∀ j,(ms j).beta.val=β (ξ j)

omit [Fintype E] in
theorem raw_profile_is_target (P : PhysicalPacking N a G) (i : Fin a)
    (g : G) (k : Page a P.copies G) {p q m : ℕ}
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ) (ms : Fin m→ModeInput a p i q)
    (hh : ModeMeaning P i g k ξ β ms) :
    (requestedProfile ms).embDomain ξ.toEmbedding=β.filter (fun v=>childTarget P i v=(g,k)) := by
  ext v
  rw [← ξ.apply_symm_apply v]
  rw [show ξ (ξ.symm v)=ξ.toEmbedding (ξ.symm v) from rfl,Finsupp.embDomain_apply,
    requestedProfile_read]
  rw [hh.exponents,Finsupp.filter_apply]
  change (if (ms (ξ.symm v)).targeted=true then β (ξ (ξ.symm v)) else 0)=
    (if childTarget P i (ξ (ξ.symm v))=(g,k) then β (ξ (ξ.symm v)) else 0)
  by_cases H : (ms (ξ.symm v)).targeted=true
  · rw [if_pos H,if_pos ((hh.target _).mp H)]
  · rw [if_neg H,if_neg (fun ht=>H ((hh.target _).mpr ht))]

theorem raw_source_is_packet {R : Type*} [CommRing R]
    (P : PhysicalPacking N a G) (i : Fin a) (g : G) (k : Page a P.copies G) {p q m : ℕ}
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ) (ms : Fin m→ModeInput a p i q)
    (hh : ModeMeaning P i g k ξ β ms) (v : PhysicalState P i g)
    (cs : List (ColsOf P i g k)) (hn : cs.Nodup) (ha : ∀ c,c∈cs) :
    (((List.ofFn ms).map (sourcedValue (cs.map (realCol P i v)))).prod:R)=
      ∏ m ∈ Finset.univ.filter (fun m=>childSource P i m=(g,k)), (stateMoment P i g p v m:R)^β m := by
  rw [List.map_ofFn,List.prod_ofFn,Finset.prod_filter]
  apply Fintype.prod_equiv ξ
  intro j
  simp only [Function.comp_apply,sourcedValue]
  by_cases H : (ms j).sourced=true
  · have H' := (hh.source j).mp H
    rw [if_pos H,if_pos H',hh.tile,hh.order,hh.exponents,
      sourceMoment_physical P i p v (ξ j) H' cs hn ha]
  · have H' : childSource P i (ξ j)≠(g,k) := fun h=>H ((hh.source j).mpr h)
    rw [if_neg H,if_neg H']

omit [Fintype E] in
theorem raw_cross_is_packet {R : Type*} [CommRing R]
    (P : PhysicalPacking N a G) (i : Fin a) (g : G) (k : Page a P.copies G) {p q m : ℕ}
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ) (ms : Fin m→ModeInput a p i q)
    (hh : ModeMeaning P i g k ξ β ms)
    {t : ℤ} (htM : t∈grid a) (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (hnil : (2:R)^p=0) (z : R) (v : PhysicalState P i g) (r : RowsOf P i g k) (j : Fin m) :
    crossMeaning t z (realRow P i v r) (ms j)=scaledRow P.mask i ht hv p hnil z (P.seat r.val) (ξ j) := by
  have hh' : rowBlock P.mask i (P.seat r.val)=target P.mask i (ξ j) ↔ childTarget P i (ξ j)=(g,k) := by
    have H : (rowBlock P.mask i (P.seat r.val)).swap=(g,k) := r.property
    unfold childTarget
    constructor
    · intro hr
      exact (congrArg Prod.swap hr).symm.trans H
    · intro h
      exact Prod.swap_injective (H.trans h.symm)
  unfold crossMeaning
  by_cases h : (ms j).targeted=true
  · rw [if_pos h,realRow_index,hh.tile,hh.order,
      scaled_on_target_is_crossCell P.mask i htM ht hv p hnil z _ _ (hh'.mpr ((hh.target j).mp h))]
  · rw [if_neg h,scaled_off_target_zero P.mask i ht hv p hnil z _ _
      (fun he=>h ((hh.target j).mpr (hh'.mp he)))]

#print axioms typedRow_poly
#print axioms rename_signed_row
#print axioms raw_profile_is_target
#print axioms raw_source_is_packet
#print axioms raw_cross_is_packet
end J6R18ChildWrite




