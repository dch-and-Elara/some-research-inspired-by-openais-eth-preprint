import J6R22ActiveJetFold
import J6R21LeafWidth

/-! Literal coefficient payloads of the finite native jet representation.
This counts bits in the stored coefficient blocks, not object headers,
control frames, retained step counters, or workspace of the gates. -/
namespace J6R49NonModeStack
open A1R10 AOracleMachineTime J6R21Leaf J6R22Active
set_option autoImplicit false
set_option warningAsError true

variable {p ell k : ℕ} {fw : List (A1R10.Word p)}

abbrev scalarWidth (e ell p : ℕ) : ℕ := ell * (e * p)

def coeffPayload (values : List (UVBlock fw ell)) : List Bool :=
  values.flatMap leafPayload

theorem coeff_payload_length (values : List (UVBlock fw ell)) :
    (coeffPayload values).length=values.length*scalarWidth fw.length ell p := by
  induction values with
  | nil => simp [coeffPayload]
  | cons x xs ih =>
    change ((leafPayload x) ++ coeffPayload xs).length=
      (xs.length+1)*scalarWidth fw.length ell p
    rw [List.length_append,leaf_payload_width,ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

def jetPayload (x : JetTape fw ell k) : List Bool := coeffPayload x.val

theorem jet_payload_length (x : JetTape fw ell k) :
    (jetPayload x).length=k*scalarWidth fw.length ell p :=
  (coeff_payload_length x.val).trans (congrArg (fun n=>n*scalarWidth fw.length ell p) x.property)

def keptPayload (xs : List (Meter (JetTape fw ell k))) : List Bool :=
  xs.flatMap (fun x=>jetPayload x.result)

theorem kept_payload_length (xs : List (Meter (JetTape fw ell k))) :
    (keptPayload xs).length=xs.length*(k*scalarWidth fw.length ell p) := by
  induction xs with
  | nil => simp [keptPayload]
  | cons x xs ih =>
    change ((jetPayload x.result) ++ keptPayload xs).length=
      (xs.length+1)*(k*scalarWidth fw.length ell p)
    rw [List.length_append,jet_payload_length,ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

/-- The actual pre-truncation product used by `jetMult` has two tapes'
worth of coefficient payload. This does not cover scratch inside that
convolution, or the simultaneously retained operands. -/
theorem raw_jet_convolution_payload (hp : 0<p) (he : 0<fw.length)
    (x y : JetTape fw ell k) :
    (coeffPayload (convolve (jetGates hp he ell) x.val y.val).result).length=
      (k+k)*scalarWidth fw.length ell p := by
  have h := (convolve_exact (jetOps hp he ell) x.val y.val).1
  change (convolve (jetGates hp he ell) x.val y.val).result.length=_ at h
  rw [coeff_payload_length,h,x.property,y.property]

#print axioms coeff_payload_length
#print axioms jet_payload_length
#print axioms kept_payload_length
#print axioms raw_jet_convolution_payload
end J6R49NonModeStack
