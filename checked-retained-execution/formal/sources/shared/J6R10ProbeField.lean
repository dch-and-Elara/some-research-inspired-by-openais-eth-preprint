import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Perfect
import NativeProbeRing

/-!
# Existence of the source probe extension

For every positive degree the finite field has a power basis. Its
minimal polynomial over ZMod 2 is monic and irreducible of exactly
that degree. The maintained source polynomial is the explicit
coefficientwise 0/1 integer lift. This is an existence theorem, not
a deterministic search-time bound.
-/

open scoped Polynomial BigOperators

namespace J6R10ProbeField
open Polynomial

/-- A finite field of any requested positive binary extension degree
gives a polynomial, not only an abstract domain of suitable size. -/
theorem exists_binary_irreducible (e : ℕ) (he : 0<e) :
    ∃ g : (ZMod 2)[X], g.Monic ∧ g.natDegree=e ∧ Irreducible g := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E := GaloisField 2 e
  let B := Field.powerBasisOfFiniteOfSeparable (ZMod 2) E
  have hI : IsIntegral (ZMod 2) B.gen := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly (ZMod 2) B.gen,minpoly.monic hI,?_,minpoly.irreducible hI⟩
  exact B.natDegree_minpoly.trans (B.finrank.symm.trans (GaloisField.finrank 2 he.ne'))

/-- Finite integer representation; every coefficient is literally 0 or 1. -/
noncomputable def liftBinary (g : (ZMod 2)[X]) : ℤ[X] :=
  ∑ j ∈ Finset.range (g.natDegree+1), monomial j ((g.coeff j).val:ℤ)

theorem liftBinary_coeff (g : (ZMod 2)[X]) (j : ℕ) :
    (liftBinary g).coeff j=(g.coeff j).val := by
  unfold liftBinary
  rw [Polynomial.finset_sum_coeff]
  by_cases h : j≤g.natDegree
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      exact coeff_monomial_of_ne _ hk.symm
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · have h0 : g.coeff j=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h0,ZMod.val_zero,Int.ofNat_zero]
    apply Finset.sum_eq_zero
    intro k hk
    exact coeff_monomial_of_ne _ (by have := Finset.mem_range.mp hk; omega)

theorem liftBinary_digits (g : (ZMod 2)[X]) (j : ℕ) :
    (liftBinary g).coeff j=0 ∨ (liftBinary g).coeff j=1 := by
  have h : (g.coeff j).val<2 := ZMod.val_lt _
  rw [liftBinary_coeff]
  omega

theorem liftBinary_monic {g : (ZMod 2)[X]} (hm : g.Monic) :
    (liftBinary g).Monic ∧ (liftBinary g).natDegree=g.natDegree := by
  have ht : (liftBinary g).coeff g.natDegree=1 := by
    rw [liftBinary_coeff,hm.coeff_natDegree]
    decide
  have hd : (liftBinary g).natDegree=g.natDegree := by
    apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      rw [liftBinary_coeff,coeff_eq_zero_of_natDegree_lt hj,ZMod.val_zero,Int.ofNat_zero]
    · exact le_natDegree_of_ne_zero (by rw [ht]; decide)
  refine ⟨?_,hd⟩
  unfold Monic leadingCoeff
  rw [hd,ht]

theorem residue_liftBinary (g : (ZMod 2)[X]) :
    NativeProbeRing.residuePoly (liftBinary g)=g := by
  ext j
  rw [NativeProbeRing.residuePoly,coeff_map,liftBinary_coeff]
  change (((g.coeff j).val:ℤ):ZMod 2)=g.coeff j
  rw [Int.cast_natCast,ZMod.natCast_zmod_val]

/-- The exact monic defining polynomial used by NativeProbeRing. -/
theorem exists_integral_probe_poly (e : ℕ) (he : 0<e) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree=e ∧
      Irreducible (NativeProbeRing.residuePoly f) ∧
      (∀ j, f.coeff j=0 ∨ f.coeff j=1) := by
  obtain ⟨g,hg,hd,hi⟩ := exists_binary_irreducible e he
  obtain ⟨hf,hfdeg⟩ := liftBinary_monic hg
  exact ⟨liftBinary g,hf,hfdeg.trans hd,
    by rwa [residue_liftBinary],liftBinary_digits g⟩

/-- The source receives a true binary power-basis probe family at
every positive precision, with invertible pairwise differences.
No assumption about finding the irreducible polynomial efficiently
or acquiring the corresponding registers enters this theorem. -/
theorem printed_probe_extension (e p d : ℕ) (he : 0<e) (hp : 0<p)
    (hfit : d≤2^e) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree=e ∧ Irreducible (NativeProbeRing.residuePoly f) ∧
      ∃ words : Fin d → (Fin f.natDegree → Bool),
        ∀ i j : Fin d, i≠j →
          IsUnit (NativeProbeRing.probe p f (words j)-NativeProbeRing.probe p f (words i)) := by
  obtain ⟨f,hf,hd,hi,_digits⟩ := exists_integral_probe_poly e he
  haveI : Fact (Irreducible (NativeProbeRing.residuePoly f)) := ⟨hi⟩
  have hdfit : d≤2^f.natDegree := by rwa [hd]
  exact ⟨f,hf,hd,hi,NativeProbeRing.chosenRep f.natDegree d hdfit,
    NativeProbeRing.chosenProbes_units p hp f hf (hd.symm ▸ he) d hdfit⟩

/-- In the printed regime the size/degree bound supplies the menu
cardinality condition automatically. -/
theorem source_probe_extension (s ellLog p d : ℕ) (hs : s≤2^ellLog)
    (hd : d≤s^4) (he : 0<ellLog) (hp : 0<p) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree=4*ellLog ∧
      Irreducible (NativeProbeRing.residuePoly f) ∧
      ∃ words : Fin d → (Fin f.natDegree → Bool),
        ∀ i j : Fin d, i≠j →
          IsUnit (NativeProbeRing.probe p f (words j)-NativeProbeRing.probe p f (words i)) :=
  printed_probe_extension (4*ellLog) p d (by omega) hp (NativeProbeRing.printed_fit s ellLog d hs hd)

/-- The residue quotient has exactly 2^e elements, not just at least
the number of probes the source asks for. This uses the monic
power-basis coordinate equivalence. -/
noncomputable def residueCoordinates (f : ℤ[X]) (hf : f.Monic) :
    NativeProbeRing.Residue f ≃ (Fin (NativeProbeRing.residuePoly f).natDegree → ZMod 2) :=
  ((AdjoinRoot.powerBasisAux' (hf.map (Int.castRingHom (ZMod 2)))).equivFun).toEquiv

theorem residue_card (f : ℤ[X]) (hf : f.Monic) :
    Nat.card (NativeProbeRing.Residue f)=2^f.natDegree := by
  have hdeg : (NativeProbeRing.residuePoly f).natDegree=f.natDegree :=
    hf.natDegree_map _
  rw [Nat.card_congr (residueCoordinates f hf),Nat.card_eq_fintype_card,
    Fintype.card_fun,Fintype.card_fin,ZMod.card,hdeg]

/-- The available binary probe words exhaust, not merely inject into,
the actual residue field, uniformly in the positive input precision. -/
theorem every_residue_is_binary (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    (p : ℕ) (hp : 0<p) :
    Function.Bijective (NativeProbeRing.residueMap p hp f ∘ NativeProbeRing.probe p f) := by
  letI : Fintype (NativeProbeRing.Residue f) :=
    Fintype.ofEquiv _ (residueCoordinates f hf).symm
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨NativeProbeRing.binary_residues_injective p hp f hf hd,?_⟩
  rw [← Nat.card_eq_fintype_card (α:=NativeProbeRing.Residue f),residue_card f hf]
  exact NativeProbeRing.menu_card _

#print axioms exists_binary_irreducible
#print axioms liftBinary_coeff
#print axioms liftBinary_monic
#print axioms residue_liftBinary
#print axioms exists_integral_probe_poly
#print axioms printed_probe_extension
#print axioms source_probe_extension
#print axioms residue_card
#print axioms every_residue_is_binary

end J6R10ProbeField

