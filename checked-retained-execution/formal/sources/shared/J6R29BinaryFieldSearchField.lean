
import J6R28GeneratedRootFrameLiteral
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

/-! The original search space is complete, over F₂ and only for
monic divisors at most half the degree. Finite-field existence is a
theorem from Galois fields and primitive elements, not a success axiom. -/
namespace J6R29BinaryFieldSearch
open scoped Polynomial
open Polynomial J6R28GeneratedRootFrame A1R10
set_option maxHeartbeats 6300000
set_option maxRecDepth 1800

theorem binary_field_coefficient (c : ZMod 2) :
    ∃ b : Bool,c=(if b then 1 else 0) := by
  have h := ZMod.val_lt c
  have z := ZMod.natCast_zmod_val c
  by_cases hz : c.val=0
  · refine ⟨false,?_⟩
    rw [hz] at z
    exact z.symm
  · have h1 : c.val=1 := by omega
    refine ⟨true,?_⟩
    rw [h1] at z
    exact z.symm

theorem lower_tape_complete (n : ℕ) (p : (ZMod 2)[X])
    (h : ∀ j,n≤j→p.coeff j=0) :
    ∃ bs : List Bool,bs.length=n ∧ lowerBinary (ZMod 2) bs=p := by
  induction n generalizing p with
  | zero =>
    refine ⟨[],rfl,?_⟩
    ext j
    simp [lowerBinary,h j (Nat.zero_le _)]
  | succ n ih =>
    let q := p-monomial n (p.coeff n)
    have hq : ∀ j,n≤j→q.coeff j=0 := by
      intro j le
      change (p-monomial n (p.coeff n)).coeff j=0
      by_cases H : j=n
      · subst j
        rw [coeff_sub,coeff_monomial,if_pos rfl,sub_self]
      · rw [coeff_sub,h j (by omega),coeff_monomial_of_ne _ H,sub_zero]
    obtain ⟨bs,l,eq⟩ := ih q hq
    obtain ⟨b,hb⟩ := binary_field_coefficient (p.coeff n)
    refine ⟨b::bs,by simp [l],?_⟩
    rw [lowerBinary,l,eq,←hb]
    unfold q
    abel

theorem monic_binary_complete (p : (ZMod 2)[X]) (hp : p.Monic) :
    ∃ bits : List Bool,bits.length=p.natDegree ∧ binaryPolynomial (ZMod 2) bits=p := by
  let n := p.natDegree
  let q := p-monomial n 1
  have hc : p.coeff n=1 := hp
  have high : ∀ j,n≤j→q.coeff j=0 := by
    intro j h
    change (p-monomial n 1).coeff j=0
    by_cases e : j=n
    · subst j
      rw [coeff_sub,hc,coeff_monomial,if_pos rfl,sub_self]
    · have lh : p.natDegree<j := by change n<j; omega
      rw [coeff_sub,coeff_eq_zero_of_natDegree_lt lh,coeff_monomial_of_ne _ e,sub_zero]
  obtain ⟨bits,hlen,he⟩ := lower_tape_complete n q high
  refine ⟨bits,hlen,?_⟩
  rw [binaryPolynomial,hlen,he]
  unfold q
  abel

theorem proper_binary_divisors (bits : List Bool) (he : 0<bits.length) :
    Irreducible (binaryPolynomial (ZMod 2) bits) ↔
     ∀ g : List Bool,0<g.length→g.length≤bits.length/2→
        ¬binaryPolynomial (ZMod 2) g ∣ binaryPolynomial (ZMod 2) bits := by
  let f := binaryPolynomial (ZMod 2) bits
  have hf : f.Monic ∧ f.natDegree=bits.length := binary_monic_degree (ZMod 2) bits
  have H : f≠1 := by
    intro e
    rw [e,natDegree_one] at hf
    omega
  have test := hf.1.irreducible_iff_lt_natDegree_lt H
  rw [hf.2] at test
  refine test.trans ⟨?_,?_⟩
  · intro h d hd hb
    have x := binary_monic_degree (ZMod 2) d
    exact h _ x.1 (Finset.mem_Ioc.mpr ⟨x.2.symm ▸ hd,x.2.symm ▸ hb⟩)
  · intro h q hq hs
    obtain ⟨b,hb,eq⟩ := monic_binary_complete q hq
    rw [←eq]
    exact h b (hb.symm ▸ (Finset.mem_Ioc.mp hs).1) (hb.symm ▸ (Finset.mem_Ioc.mp hs).2)

theorem exists_monic_binary_field_polynomial (e : ℕ) (he : 0<e) :
    ∃ p : (ZMod 2)[X],p.Monic ∧ p.natDegree=e ∧ Irreducible p := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let K := ZMod 2
  let E := GaloisField 2 e
  obtain ⟨a,ha⟩ := Field.exists_primitive_element_of_finite_top K E
  have int : IsIntegral K a := IsIntegral.of_finite K a
  have dim := IntermediateField.adjoin.finrank int
  rw [ha,IntermediateField.finrank_top',GaloisField.finrank 2 he.ne'] at dim
  exact ⟨minpoly K a,minpoly.monic int,dim.symm,minpoly.irreducible int⟩

theorem exists_binary_field_tape (e : ℕ) (he : 0<e) :
    ∃ bits : Word e,Irreducible (binaryPolynomial (ZMod 2) bits.val) := by
  obtain ⟨p,hm,hd,hi⟩ := exists_monic_binary_field_polynomial e he
  obtain ⟨b,l,v⟩ := monic_binary_complete p hm
  exact ⟨⟨b,l.trans hd⟩,v.symm ▸ hi⟩

theorem source_residue_of_tape {e : ℕ} (bits : Word e) :
    NativeProbeRing.residuePoly (chosenBinaryPolynomial bits)=binaryPolynomial (ZMod 2) bits.val :=
  binary_polynomial_map (Int.castRingHom (ZMod 2)) bits.val

#print axioms lower_tape_complete
#print axioms monic_binary_complete
#print axioms proper_binary_divisors
#print axioms exists_monic_binary_field_polynomial
#print axioms exists_binary_field_tape
#print axioms source_residue_of_tape
end J6R29BinaryFieldSearch
