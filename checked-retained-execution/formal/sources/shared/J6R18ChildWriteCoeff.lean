import J6PacketCoefficientBridge

/-! Finite affine coefficient extraction written as a depth-first row
expansion. An omitted choice contributes exponent zero; a crossing
choice contributes one unit exponent. The coefficient theorem does
not require any free polynomial-operation gate in the later machine. -/
namespace J6R18ChildWrite
open scoped Classical BigOperators
open MvPolynomial J6PacketCoefficientBridge

variable {A R : Type*} [CommRing R]

noncomputable def exponents (choices : List (Option A)) : A→₀ℕ :=
  (choices.map exponent).sum

noncomputable def rowPoly (opts : List (Option A × R)) : MvPolynomial A R :=
  (opts.map (fun r=>monomial (exponent r.1) r.2)).sum

noncomputable def rowsPoly (rows : List (List (Option A × R))) : MvPolynomial A R :=
  (rows.map rowPoly).prod

noncomputable def expansion (β : A→₀ℕ) :
    List (List (Option A × R)) → List (Option A) → R → R
  | [],pre,acc => if exponents pre=β then acc else 0
  | row::rs,pre,acc =>
    (row.map (fun t=>expansion β rs (t.1::pre) (acc*t.2))).sum

theorem exponent_list_cons (x : Option A) (xs : List (Option A)) :
    exponents (x::xs)=exponent x+exponents xs := rfl

theorem row_distribution (β e : A→₀ℕ) (acc : R)
    (opts : List (Option A × R)) (tail : MvPolynomial A R) :
    (opts.map (fun c=>coeff β (monomial (exponent c.1+e) (acc*c.2)*tail))).sum=
      coeff β (monomial e acc*(rowPoly opts*tail)) := by
  induction opts with
  | nil => simp [rowPoly]
  | cons x xs ih =>
    change coeff β (monomial (exponent x.1+e) (acc*x.2)*tail)+
      (xs.map (fun c=>coeff β (monomial (exponent c.1+e) (acc*c.2)*tail))).sum=
      coeff β (monomial e acc*((monomial (exponent x.1) x.2+rowPoly xs)*tail))
    rw [ih,add_mul,mul_add,coeff_add]
    simp only [← mul_assoc,monomial_mul,add_comm e]

theorem expansion_exact (β : A→₀ℕ) (rows : List (List (Option A × R)))
    (pre : List (Option A)) (acc : R) :
    expansion β rows pre acc=coeff β (monomial (exponents pre) acc*rowsPoly rows) := by
  induction rows generalizing pre acc with
  | nil =>
    simp [expansion,rowsPoly,coeff_monomial]
  | cons row rows ih =>
    change (row.map (fun t=>expansion β rows (t.1::pre) (acc*t.2))).sum=
      coeff β (monomial (exponents pre) acc * (rowPoly row*rowsPoly rows))
    simp only [ih,exponent_list_cons]
    exact row_distribution β (exponents pre) acc row (rowsPoly rows)

theorem coefficients_exact (β : A→₀ℕ) (rows : List (List (Option A × R))) :
    expansion β rows [] 1=coeff β (rowsPoly rows) := by
  simpa [exponents] using expansion_exact β rows [] (1:R)

#print axioms row_distribution
#print axioms expansion_exact
#print axioms coefficients_exact
end J6R18ChildWrite

