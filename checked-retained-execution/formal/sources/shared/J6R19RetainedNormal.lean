import J6R18ChildWriteHost
import A1R10Readout

/-! Canonical sections commute with a normalized descending register.
The function placed at each coefficient need not preserve addition. -/
namespace J6R19Retained
open scoped Polynomial BigOperators
open Polynomial A1R10 AOracleMachineTime AOracleCoordinates
open J6R9Recursive J6R18ChildWrite

theorem section_coeff {A B : Type*} [CommRing A] [CommRing B]
    (l : B→A) (h0 : l 0=0) (P : B[X]) (n : ℕ) :
    (polynomialSection l P).coeff n=l (P.coeff n) := by
  classical
  unfold polynomialSection
  rw [finset_sum_coeff]
  by_cases H : n∈P.support
  · rw [Finset.sum_eq_single_of_mem n H]
    · simp
    · intro j _ hj
      simp [coeff_monomial,hj]
  · rw [notMem_support_iff.mp H,h0]
    apply Finset.sum_eq_zero
    intro j hj
    have h : n≠j := fun e=>H (e.symm ▸ hj)
    simp [coeff_monomial,Ne.symm h]

theorem section_push {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (m : A→+*C) (l : B→A) (P : B[X]) :
    (polynomialSection l P).map m=polynomialSection (m ∘ l) P := by
  simp only [polynomialSection,Polynomial.map_sum,Polynomial.map_monomial,Function.comp_apply]

theorem section_decode_map {A B R S T V : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing V]
    (oi : Ops A R) (oo : Ops B T) (mi : R→+*S) (mo : T→+*V)
    (l : S→V) (hl : l 0=0) (f : A→B)
    (hf : ∀ w,l (mi (oi.read w))=mo (oo.read (f w))) (xs : List A) :
    polynomialSection l ((decode oi xs).map mi)=(decode oo (xs.map f)).map mo := by
  ext n
  rw [section_coeff l hl,coeff_map,coeff_map]
  induction xs with
  | nil => simp [decode,hl]
  | cons w ws ih =>
    simp only [decode,List.map_cons,List.length_map,coeff_add]
    by_cases hn : n=ws.length
    · subst n
      rw [decode_coeff_zero oi ws _ le_rfl,decode_coeff_zero oo (ws.map f) _ (by simp)]
      simpa [coeff_monomial] using hf w
    · simp [coeff_monomial,Ne.symm hn,ih]

theorem normal_mapped {A R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (oi : Ops A R) (mi : R→+*S) {P : S[X]} (hp : P.Monic) (xs : List A)
    (h : xs.length≤P.natDegree) :
    AdjoinRoot.modByMonicHom hp (AdjoinRoot.mk P ((decode oi xs).map mi))=(decode oi xs).map mi := by
  rw [AdjoinRoot.modByMonicHom_mk]
  refine (modByMonic_eq_self_iff hp).mpr ?_
  rw [degree_eq_natDegree hp.ne_zero,degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_map,decode_coeff_zero oi xs n (h.trans hn),map_zero]

def transportU {R : Type*} [CommRing R] {P Q : R[X]} (h : P=Q) :
    AdjoinRoot P ≃+* AdjoinRoot Q := by
  cases h
  exact RingEquiv.refl _

theorem transportU_mk {R : Type*} [CommRing R] {P Q : R[X]} (h : P=Q) (a : R[X]) :
    transportU h (AdjoinRoot.mk P a)=AdjoinRoot.mk Q a := by
  cases h
  rfl

theorem castBox_mk {p ell : ℕ} {P Q : (ZMod (2^p))[X]} (h : P=Q)
    (a : (AdjoinRoot P)[X]) :
    castBox h (AdjoinRoot.mk (X^ell) a)=
      AdjoinRoot.mk (X^ell) (a.map (transportU h).toRingHom) := by
  cases h
  simp [castBox,transportU]

#print axioms section_coeff
#print axioms section_push
#print axioms section_decode_map
#print axioms normal_mapped
#print axioms transportU_mk
#print axioms castBox_mk
end J6R19Retained


