import J6LiteralCoeff
import J6RecursiveMenu

namespace J6ProfileMenu
open scoped Classical BigOperators
open MvPolynomial J6ActiveProfile J6LiteralCoeff J6BlockFactor J6PacketCoefficientBridge
variable {R I M K : Type*} [CommRing R] [Fintype I] [Fintype M]

noncomputable def code (b : M → Fin (Fintype.card I+1)) : M →₀ ℕ :=
  profileFinsupp b

omit [CommRing R] in
theorem code_value (b : M → Fin (Fintype.card I+1)) (m : M) :
    code b m = (b m).val := by simp [code,profileFinsupp]

omit [CommRing R] in
theorem code_injective : Function.Injective (code (I:=I) (M:=M)) := by
  intro b c h
  funext m
  apply Fin.ext
  simpa only [code_value] using congrArg (fun x : M →₀ ℕ => x m) h

omit [CommRing R] in
theorem weight_code (w : M → ℕ) (b : M → Fin (Fintype.card I+1)) :
    J6RecursiveMenu.weighted w (code b) = profileWeight w b := by
  simp only [J6RecursiveMenu.weighted, profileWeight, code_value, Nat.mul_comm]

omit [CommRing R] in
theorem code_image_iff (b : M →₀ ℕ) :
    (∃ x : M → Fin (Fintype.card I+1), code x = b) ↔
      ∀ m, b m ≤ Fintype.card I := by
  constructor
  · rintro ⟨x,rfl⟩ m
    rw [code_value]
    exact Nat.lt_succ_iff.mp (x m).isLt
  · intro h
    refine ⟨fun m => ⟨b m,Nat.lt_succ_of_le (h m)⟩, ?_⟩
    ext m
    rw [code_value]

/-- The printed mode menu contains larger exponents than a row allocation
can realize. It is safe to add these profiles once their child product
has been proved zero, rather than silently restricting the source menu. -/
theorem extend_to_printed
    (w : M → ℕ) (hw : ∀ m, 0 < w m) (p : ℕ)
    (value : (M →₀ ℕ) → R)
    (hlarge : ∀ beta, (∃ m, Fintype.card I < beta m) → value beta = 0) :
    (∑ b : M → Fin (Fintype.card I+1),
      if profileWeight w b < p then value (code b) else 0) =
      ∑ beta ∈ J6RecursiveMenu.menu p w, value beta := by
  classical
  rw [← Finset.sum_filter]
  let small := (Finset.univ : Finset (M → Fin (Fintype.card I+1))).filter
    (fun b => profileWeight w b < p)
  calc
    (∑ b ∈ small, value (code b)) = ∑ beta ∈ small.image code, value beta := by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => code_injective h)
    _ = _ := by
      refine Finset.sum_subset ?_ ?_
      · intro beta h
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
        rw [J6RecursiveMenu.exact_printed_menu _ _ hw,weight_code]
        exact (Finset.mem_filter.mp hb).2
      · intro beta hbeta hnot
        apply hlarge
        by_contra! h
        obtain ⟨b,rfl⟩ := (code_image_iff (I:=I) beta).mpr h
        apply hnot
        rw [J6RecursiveMenu.exact_printed_menu _ _ hw,weight_code] at hbeta
        exact Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbeta⟩,rfl⟩

omit [Fintype I] in
theorem too_many_target_rows (s : Finset I) (f : I → Option M → R)
    (beta : M →₀ ℕ) (m : M) (h : s.card < beta m) :
    coeff beta (∏ i ∈ s, ∑ v : Option M, monomial (exponent v) (f i v)) = 0 := by
  classical
  rw [← Finset.prod_coe_sort]
  rw [coeff_allocations]
  apply Finset.sum_eq_zero
  intro x _
  have hc : count x m ≤ s.card := by
    unfold count
    simpa only [Finset.card_univ,Fintype.card_coe] using
      (Finset.card_filter_le (s := (Finset.univ : Finset {i // i ∈ s})) (fun i => x i = some m))
  rw [if_neg]
  intro ha
  rw [ha m] at hc
  exact (Nat.not_lt_of_ge hc) h
  
#print axioms code_value
#print axioms code_injective
#print axioms weight_code
#print axioms code_image_iff
#print axioms extend_to_printed
#print axioms too_many_target_rows
end J6ProfileMenu
