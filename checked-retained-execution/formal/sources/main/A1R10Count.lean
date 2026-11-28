import A1R10Threshold
import AOracleSuccinct

/-! Exact unsigned counter for one coordinate after executing the
double-quotient tape arithmetic. Only parsing, legality and the row
factor tape are supplied. Tape generation is not inferred. -/

open scoped BigOperators
namespace A1R10
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
open AOracleThreshold AOracleSuccinct AOracleWitness

def thresholdBits {p : ℕ} (d : AOracleThreshold.Word p) : Word p :=
  ⟨encodeBits p d.val,encodeBits_length p _⟩

def uvTapeVerifier {D W : Type*} {p : ℕ} (hp : 0<p)
    {f : List (Word p)} {ell : ℕ} (he : 0<f.length) (hv : 0<ell)
    (parse : D → Option W) (valid : W → Bool) (t : W → List (UVBlock f ell))
    (i j : ℕ) (d : D × AOracleThreshold.Word p) : Bool :=
  match parse d.1 with
  | none => false
  | some w => valid w && (uvProductAccept hp he hv (t w) i j (thresholdBits d.2)).result

theorem uvTape_count_coordinate {D W : Type*} [Fintype D] [Fintype W] {p : ℕ}
    (hp : 0<p) {f : List (Word p)} {ell : ℕ} (he : 0<f.length) (hv : 0<ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length)
    (parse : D → Option W) (enc : W ↪ D)
    (hex : ∀ d w, parse d=some w ↔ d=enc w) (legal : W → Bool)
    (t : W → List (UVBlock f ell))
    (weight : W → Truncated (Modulus p hp f) ell)
    (hwt : ∀ w,(List.map (uvRead hp f ell) (t w)).prod=weight w)
    (i : Fin f.length) (j : Fin ell) :
    (countVerify (uvTapeVerifier hp he hv parse legal t i.val j.val) : ZMod (2^p)) =
      doubleCoord (Modulus p hp f) hf ell
        (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
        (∑ w, if legal w then weight w else 0) := by
  let ij : Fin (Modulus p hp f).natDegree × Fin ell :=
    (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
  have h : uvTapeVerifier hp he hv parse legal t i.val j.val =
      verifier parse legal (fun w => doubleCoord (Modulus p hp f) hf ell ij (weight w)) := by
    funext d
    unfold uvTapeVerifier verifier
    cases hh : parse d.1 with
    | none => rfl
    | some w =>
      have ht := (uvProductAccept_exact hp he hv (t w) i j (thresholdBits d.2) hf hd).1
      change (uvProductAccept hp he hv (t w) i.val j.val (thresholdBits d.2)).result=true ↔
        bitsValue (encodeBits p d.2.val)<(doubleCoord (Modulus p hp f) hf ell ij
          ((List.map (uvRead hp f ell) (t w)).prod)).val at ht
      rw [encodeBits_exact p _ d.2.isLt,hwt w] at ht
      apply Bool.eq_iff_iff.mpr
      simpa only [Bool.and_eq_true,decide_eq_true_eq] using and_congr_right (fun _ => ht)
  rw [h]
  exact countQuery_coordinate parse enc hex legal weight (doubleCoord (Modulus p hp f) hf ell) ij

theorem uvTape_native_register {r c m delta b p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (he : 0<f.length) (hv : 0<ell) (hf : (Modulus p hp f).Monic)
    (hd : (Modulus p hp f).natDegree=f.length) (fit : m+1≤2^b)
    (L : Recipes (Truncated (Modulus p hp f) ell) r c m delta) (beta : Fin m →₀ ℕ)
    (t : Witness r c m → List (UVBlock f ell))
    (hwt : ∀ w,(List.map (uvRead hp f ell) (t w)).prod=weight (rootTerms L) w)
    (i : Fin f.length) (j : Fin ell) :
    (countVerify (uvTapeVerifier hp he hv (parse (b := b)) (valid (rootTerms L) beta) t i.val j.val)
      : ZMod (2^p)) =
      doubleCoord (Modulus p hp f) hf ell
        (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
        (MvPolynomial.coeff beta (rootPolynomial (rootTerms L))) := by
  rw [coefficient_eq_valid_sum]
  exact uvTape_count_coordinate hp he hv hf hd parse (encode fit) (parse_exact fit)
    _ t (weight (rootTerms L)) hwt i j

#print axioms uvTape_count_coordinate
#print axioms uvTape_native_register
end A1R10
