import Normalization
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators

namespace SharpDifference

abbrev ModTwo := D ⧸ Ideal.span ({2} : Set D)

noncomputable def modTwo : D →+* ModTwo := Ideal.Quotient.mk _

noncomputable def reducePoly : LocalPoly →+* Polynomial ModTwo :=
  Polynomial.mapRingHom modTwo

theorem modTwo_two : modTwo (2 : D) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem reducePoly_natCast (n : ℕ) :
    reducePoly (n : LocalPoly) = reducePoly ((n % 2 : ℕ) : LocalPoly) := by
  have htwo : reducePoly (2 : LocalPoly) = 0 := by
    have h : Polynomial.C (2 : D) = (2 : LocalPoly) :=
      Polynomial.C_eq_natCast (R := D) 2
    rw [← h]
    change (Polynomial.C (2 : D)).map modTwo = 0
    rw [Polynomial.map_C, modTwo_two, Polynomial.C_0]
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  have h : (n : LocalPoly) = (2 : LocalPoly) * ((n / 2 : ℕ) : LocalPoly) +
      ((n % 2 : ℕ) : LocalPoly) := by exact_mod_cast hn
  calc
    _ = reducePoly ((2 : LocalPoly) * ((n / 2 : ℕ) : LocalPoly) +
      ((n % 2 : ℕ) : LocalPoly)) := congrArg reducePoly h
    _ = _ := by rw [map_add, map_mul, htwo, zero_mul, zero_add]

theorem reduce_eval_of_mod_eq {k : ℕ} (Q : MvPolynomial (Fin k) LocalPoly)
    (E F : Fin k → ℕ) (h : ∀ j, E j % 2 = F j % 2) :
    reducePoly (MvPolynomial.eval (fun j => (E j : LocalPoly)) Q) =
      reducePoly (MvPolynomial.eval (fun j => (F j : LocalPoly)) Q) := by
  have he : reducePoly.comp (MvPolynomial.eval (fun j => (E j : LocalPoly))) =
      reducePoly.comp (MvPolynomial.eval (fun j => (F j : LocalPoly))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply]
    · intro j
      simp only [RingHom.comp_apply, MvPolynomial.eval_X]
      rw [reducePoly_natCast (E j), reducePoly_natCast (F j), h j]
  exact DFunLike.congr_fun he Q

/-- Equal sizes of the true fibers allow the two binary labelings to be matched. -/
theorem perm_of_equal_true_counts {ι : Type*} [Fintype ι] (f g : ι → Bool)
    (h : (Finset.univ.filter fun i => f i = true).card =
      (Finset.univ.filter fun i => g i = true).card) :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = f i := by
  classical
  let fibers (a : ι → Bool) (b : Bool) := Finset.univ.filter fun i => a i = b
  have card_eq (a : ι → Bool) (b : Bool) :
      Fintype.card {i // a i = b} = (fibers a b).card := by
    let e : {i // a i = b} ≃ ↥(fibers a b) :=
      Equiv.subtypeEquivRight (fun i => by simp [fibers])
    exact (Fintype.card_congr e).trans (Fintype.card_coe _)
  have hc (a : ι → Bool) :
      fibers a false = Finset.univ \ fibers a true := by
    ext i
    cases hi : a i <;> simp [fibers, hi]
  have hcards (b : Bool) : (fibers f b).card = (fibers g b).card := by
    cases b
    · rw [hc f, hc g, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      exact congrArg (fun n => Finset.univ.card - n) h
    · exact h
  let e (b : Bool) : {i // f i = b} ≃ {i // g i = b} :=
    Fintype.equivOfCardEq ((card_eq f b).trans ((hcards b).trans (card_eq g b).symm))
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

noncomputable def oddCount {k : ℕ} (E : Fin k → ℕ) : ℕ :=
  (Finset.univ.filter fun i => E i % 2 = 1).card

theorem residue_depends_on_oddCount {k : ℕ} (Q : MvPolynomial (Fin k) LocalPoly)
    (hs : ∀ π : Equiv.Perm (Fin k), MvPolynomial.rename π Q = Q)
    (E F : Fin k → ℕ) (h : oddCount E = oddCount F) :
    reducePoly (MvPolynomial.eval (fun j => (E j : LocalPoly)) Q) =
      reducePoly (MvPolynomial.eval (fun j => (F j : LocalPoly)) Q) := by
  let e (i : Fin k) := decide (E i % 2 = 1)
  let f (i : Fin k) := decide (F i % 2 = 1)
  have hc : (Finset.univ.filter fun i => e i = true).card =
      (Finset.univ.filter fun i => f i = true).card := by
    simpa [e, f, oddCount] using h
  obtain ⟨π, hπ⟩ := perm_of_equal_true_counts e f hc
  have he (j : Fin k) : E j % 2 = F (π j) % 2 := by
    have hb := hπ j
    change decide (F (π j) % 2 = 1) = decide (E j % 2 = 1) at hb
    simp only [decide_eq_decide] at hb
    omega
  calc
    _ = reducePoly (MvPolynomial.eval (fun j => (F (π j) : LocalPoly)) Q) :=
      reduce_eval_of_mod_eq Q E (fun j => F (π j)) he
    _ = reducePoly (MvPolynomial.eval (fun j => (F j : LocalPoly))
          (MvPolynomial.rename π Q)) := by rw [MvPolynomial.eval_rename]; rfl
    _ = _ := by rw [hs π]

/-- Step 1, with the same symbolic quotient for every exponent list through M. -/
theorem common_symbolic_normalization (M k : ℕ) :
    ∃ Q : MvPolynomial (Fin k) LocalPoly,
      (∀ π : Equiv.Perm (Fin k), MvPolynomial.rename π Q = Q) ∧
      (∀ (E : Fin k → ℕ), (∀ j, E j ≤ M) →
        (sourceMatrix E).det =
          twoU ^ k.choose 2 * liftPoly ((Matrix.vandermonde (fun j => (E j : LocalPoly))).det) *
            liftPoly (MvPolynomial.eval (fun j => (E j : LocalPoly)) Q)) ∧
      (∀ (E F : Fin k → ℕ), oddCount E = oddCount F →
        reducePoly (MvPolynomial.eval (fun j => (E j : LocalPoly)) Q) =
          reducePoly (MvPolynomial.eval (fun j => (F j : LocalPoly)) Q)) ∧
      (∀ (E : Fin k → ℕ), Function.Injective E → (∀ j, E j ≤ M) →
        atZero (MvPolynomial.eval (fun j => (E j : LocalPoly)) Q) = 1) := by
  obtain ⟨Q, hQ, hs⟩ := exists_symmetric_alternant_quotient (fun i : Fin k => rowPoly M i.val)
  refine ⟨Q, hs, normalize_det_with_Q hQ, residue_depends_on_oddCount Q hs, ?_⟩
  intro E hE heM
  let embed : Fin k → Fin (M + 1) := fun j => ⟨E j, Nat.lt_succ_of_le (heM j)⟩
  have hcard := Fintype.card_le_of_injective embed (fun i j hij => hE (congrArg Fin.val hij))
  simp only [Fintype.card_fin] at hcard
  exact normalized_atZero hQ E hE (fun i => by have hi := i.isLt; omega)

end SharpDifference

