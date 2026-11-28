import AOracleWitness
import AOracleCoordinates

/-! Combined A1 certificate: a genuine two-cube completed coefficient in the
double quotient is exactly determined by e·ℓ finite counting replies.
Oracle calls and accepting paths are counted; the cost of the native entry
functions, the oracle itself, and the reduction to a machine model are not. -/

namespace AOracleRegister

open AOracleThreshold AOracleWitness AOracleCoordinates

theorem actual_root_register_oracle {r c m p : ℕ} (hp : 0 < p)
    (f : Polynomial (Base p)) (hf : f.Monic) (he : 0 < f.natDegree)
    (ell : ℕ) (hell : 0 < ell) (S : RootTerms r c m (Truncated f ell))
    (β : Fin m →₀ ℕ) :
    let b := Nat.clog 2 (m+1)
    let reply := fun ij => countQuery (parse (b:=b)) (valid S β)
      (fun w => doubleCoord f hf ell ij (weight S w))
    (∀ ij, (reply ij : Base p) = doubleCoord f hf ell ij
      (MvPolynomial.coeff β (rootPolynomial S))) ∧
    (∃! a : Truncated f ell, ∀ ij, doubleCoord f hf ell ij a = (reply ij : Base p)) ∧
    (∀ ij, reply ij ≤ 2^(r+c+b*r+p)) := by
  dsimp only
  let b := Nat.clog 2 (m+1)
  have fits : m+1 ≤ 2^b := min_width_fits _
  refine ⟨?_, ?_, ?_⟩
  · intro ij
    exact requested_coordinate_from_count S β fits (doubleCoord f hf ell) ij
  · exact reconstruct_from_counters hp f hf he ell hell (parse (b:=b)) (encode fits)
      (parse_exact fits) (valid S β) (weight S)
  · intro ij
    exact encoded_counter_bound (b:=b) _ _

#print axioms actual_root_register_oracle

end AOracleRegister

