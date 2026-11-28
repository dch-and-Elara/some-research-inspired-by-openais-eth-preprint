import J6R10ProbeField
import Mathlib.Logic.Equiv.Basic

/-!
# A single source probe menu with zero at every precision

NativeProbeRing.chosenRep uses an arbitrary finite enumeration.
The zero representative is installed explicitly by a permutation,
not by assuming it is already stored at the first index.
-/

namespace J6R10ProbeFieldZero
open NativeProbeRing J6R10ProbeField
open scoped Polynomial BigOperators

theorem zero_word (p : ℕ) (f : ℤ[X]) :
    probe p f (fun _ => false)=0 := by
  simp [probe,binaryPoly]

theorem units_for_injective_words (p : ℕ) (hp : 0<p) (f : ℤ[X])
    (hm : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (residuePoly f))]
    {d : ℕ} (words : Fin d → Fin f.natDegree → Bool) (hw : Function.Injective words) :
    ∀ i j : Fin d, i≠j → IsUnit (probe p f (words j)-probe p f (words i)) := by
  intro i j h
  apply unit_of_residue p hp f hm
  rw [map_sub,sub_ne_zero]
  intro he
  have hw' := (binary_residues_injective p hp f hm hd) he
  exact h (hw hw').symm

/-- Same integral polynomial and the same menu of binary words work
for all positive precisions. The chosen zero address is literal. -/
theorem zero_in_uniform_menu (e d : ℕ) (he : 0<e) (hd : 0<d) (hfit : d≤2^e) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree=e ∧ Irreducible (residuePoly f) ∧
      ∃ words : Fin d → Fin f.natDegree → Bool,
        words ⟨0,hd⟩ = (fun _ => false) ∧
        ∀ p : ℕ, 0<p →
          probe p f (words ⟨0,hd⟩)=0 ∧
          ∀ i j : Fin d, i≠j → IsUnit (probe p f (words j)-probe p f (words i)) := by
  classical
  obtain ⟨f,hf,hdeg,hi,_bits⟩ := exists_integral_probe_poly e he
  have hfpos : 0<f.natDegree := by rwa [hdeg]
  letI : Fact (Irreducible (residuePoly f)) := ⟨hi⟩
  have hfit' : d≤2^f.natDegree := by rwa [hdeg]
  let start : Fin d := ⟨0,hd⟩
  let base := chosenRep f.natDegree d hfit'
  let swap := Equiv.swap (base start) (fun _ => false)
  let words := fun i => swap (base i)
  have hwords : Function.Injective words :=
    swap.injective.comp (chosenRep_injective _ _ _)
  have hzero : words start = (fun _ => false) :=
    Equiv.swap_apply_left _ _
  refine ⟨f,hf,hdeg,hi,words,hzero,fun p hp => ⟨?_,?_⟩⟩
  · rw [show words ⟨0,hd⟩=(fun _ => false) from hzero,zero_word]
  · exact units_for_injective_words p hp f hf hfpos words hwords

theorem scalar_card (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic) :
    Nat.card (Scalar p f)=2^(p*f.natDegree) := by
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  let chart : Scalar p f ≃ (Fin (liftPoly p f).natDegree → Base p) :=
    ((AdjoinRoot.powerBasisAux' (hf.map (Int.castRingHom (Base p)))).equivFun).toEquiv
  have hd : (liftPoly p f).natDegree=f.natDegree := hf.natDegree_map _
  rw [Nat.card_congr chart,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,
    ZMod.card,hd,← pow_mul]

#print axioms zero_word
#print axioms units_for_injective_words
#print axioms zero_in_uniform_menu
#print axioms scalar_card

end J6R10ProbeFieldZero

