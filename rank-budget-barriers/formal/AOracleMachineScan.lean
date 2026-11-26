import AOracleMachine
import AOracleMachineArithmetic

/-!
# Explicit serial scanning for A1 data

The lookup trace is metered by the actual finite input list, not by
random-access table unit cost.  The final polynomial is a conservative
per-witness envelope with the genuine double quotient arithmetic
instantiated.  It is polynomial in explicit supplied payload and
parameters, not necessarily in the source CNF length.
-/

namespace AOracleMachineScan

/-- Visit entries in order, returning the answer and the number of
entries visited. One may take the entries to be individual tape bits. -/
def scan {α : Type*} : List α → ℕ → Option α × ℕ
  | [], _ => (none,0)
  | x :: _, 0 => (some x,1)
  | _ :: xs, i+1 =>
    let z := scan xs i
    (z.1,z.2+1)

theorem scan_exact {α : Type*} (xs : List α) (i : ℕ) :
    scan xs i = (xs[i]?, min (i+1) xs.length) := by
  induction xs generalizing i with
  | nil => simp [scan]
  | cons x xs ih =>
    cases i with
    | zero => simp [scan]
    | succ i =>
      rw [scan, ih]
      simp only [List.getElem?_cons_succ, List.length_cons]
      congr 1
      omega

theorem scan_payload_bound {α : Type*} (xs : List α) (i : ℕ) :
    (scan xs i).2 ≤ xs.length := by
  rw [scan_exact]
  exact min_le_right _ _

open AOracleMachine AOracleMachineArithmetic

/-- Upper envelope in a bit-serial word cost model; indexing/addresses
are charged rather than regarded as free unit-time random access. -/
def verifierEnvelope (r c m b h e ell p : ℕ) : ℕ :=
  serialEnvelope r c m b h p (payloadBits r c m e ell p h)
    (e*ell*p) (doubleMulEnvelope e ell p)

/-- Include the dimensions/address widths as explicit parameters even
for degenerate zero-size tables and untrusted headers. -/
def verifierSize (r c m b h e ell p : ℕ) : ℕ :=
  r+c+m+b+h+p+payloadBits r c m e ell p h+e*ell*p+e+ell+1

theorem verifierEnvelope_poly (r c m b h e ell p : ℕ) :
    verifierEnvelope r c m b h e ell p ≤ 60*verifierSize r c m b h e ell p ^ 7 := by
  let z := verifierSize r c m b h e ell p
  have hz : 1 ≤ z := by dsimp [z, verifierSize]; omega
  have h1 : 2+3*r ≤ 3*z := by dsimp [z, verifierSize]; omega
  have h2 : payloadBits r c m e ell p h+1 ≤ z := by dsimp [z, verifierSize]; omega
  have h3 : r+c+b+h+e*ell*p+1 ≤ z := by dsimp [z, verifierSize]; omega
  have h4 : 1+2*r ≤ 2*z := by dsimp [z, verifierSize]; omega
  have he : e+1 ≤ z := by dsimp [z, verifierSize]; omega
  have hl : ell+1 ≤ z := by dsimp [z, verifierSize]; omega
  have hp : p+1 ≤ z := by dsimp [z, verifierSize]; omega
  have h5 : doubleMulEnvelope e ell p ≤ 25*z^6 := by
    refine (doubleMulEnvelope_le e ell p).trans ?_
    calc
      _ ≤ 25*z^2*z^2*z^2 := by
        gcongr
      _ = _ := by ring
  have h6 : r ≤ z := by dsimp [z, verifierSize]; omega
  have h7 : e*ell*p+1 ≤ z := by dsimp [z, verifierSize]; omega
  have h8 : r*m+m+r+1 ≤ z*z := by
    simpa [Nat.add_mul, Nat.mul_add, mul_one, one_mul, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using
      Nat.mul_le_mul (show r+1 ≤ z by dsimp [z, verifierSize]; omega)
        (show m+1 ≤ z by dsimp [z, verifierSize]; omega)
  have h9 : r+c+b+h+p+1 ≤ z := by dsimp [z, verifierSize]; omega
  have ha := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hb := Nat.mul_le_mul h4 h5
  have hc := Nat.mul_le_mul h6 h7
  have hd := Nat.mul_le_mul h8 h9
  have hz2 : z^2 ≤ z^7 := Nat.pow_le_pow_right hz (by decide)
  have hz3 : z^3 ≤ z^7 := Nat.pow_le_pow_right hz (by decide)
  change _ ≤ 60*z^7
  unfold verifierEnvelope serialEnvelope
  nlinarith

#print axioms scan_exact
#print axioms scan_payload_bound
#print axioms verifierEnvelope_poly

end AOracleMachineScan

