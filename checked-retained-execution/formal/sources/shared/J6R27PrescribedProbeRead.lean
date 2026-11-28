
import J6R27PrescribedProbeBits
import J6R26StablePreparedRootInput

/-! The positive prefix represents distinct nonzero binary
representatives in the literal root field coordinate order. Reads use
the existing sequential bit-word scanner, not a numeric sample oracle. -/
namespace J6R27PrescribedProbe
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R14ZeroMode J6R26StablePreparedRoot
set_option maxHeartbeats 4200000
set_option linter.unusedSectionVars false

def bitAt (e j : ℕ) (k : Fin e) : Bool :=
  (encoded e j).val[k.val]'((encoded e j).property.symm ▸ k.isLt)

theorem bit_word_exact (e j : ℕ) : List.ofFn (bitAt e j)=(encoded e j).val := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,(encoded e j).property]
  · intro i il ir
    rw [List.getElem_ofFn]
    rfl

theorem bits_false_vector (e : ℕ) :
    bitsValue (List.ofFn (fun _ : Fin e=>false))=0 := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [List.ofFn_succ]
    change 0+2*bitsValue (List.ofFn (fun _ : Fin e=>false))=0
    rw [ih]

def canonicalPrescribed (f : ℤ[X]) (D : ℕ) (fit : D+1<2^f.natDegree) : Prescribed f D where
  word := fun i=>bitAt f.natDegree (i.val+1)
  distinct := by
    intro i j eq
    have e := congrArg List.ofFn eq
    rw [bit_word_exact,bit_word_exact] at e
    have a : i.val+1<2^f.natDegree := (Nat.succ_le_of_lt i.isLt).trans_lt fit
    have b : j.val+1<2^f.natDegree := (Nat.succ_le_of_lt j.isLt).trans_lt fit
    have c := congrArg bitsValue e
    change bitsValue (encodeBits f.natDegree (i.val+1)) =
      bitsValue (encodeBits f.natDegree (j.val+1)) at c
    rw [encodeBits_exact _ _ a,encodeBits_exact _ _ b] at c
    exact Fin.ext (by omega)
  excludesZero := by
    intro i eq
    have e := congrArg List.ofFn eq
    rw [bit_word_exact] at e
    have a : i.val+1<2^f.natDegree := (Nat.succ_le_of_lt i.isLt).trans_lt fit
    have c := congrArg bitsValue e
    change bitsValue (encodeBits f.natDegree (i.val+1)) =
      bitsValue (List.ofFn (fun _ : Fin f.natDegree=>false)) at c
    rw [encodeBits_exact _ _ a,bits_false_vector] at c
    omega

theorem positive_width_of_fit (e D : ℕ) (fit : D+1<2^e) : 0<e := by
  by_contra h
  have zero : e=0 := by omega
  rw [zero,pow_zero] at fit
  omega

def readTape {e D : ℕ} (he : 0<e) (raw : List (Word e)) (i : Fin (D+1)) :
    Meter (Word e) :=
  scanWord (wordOps e he).toGates i.val raw

theorem read_tape_exact (e D : ℕ) (he : 0<e) (raw : List (Word e))
    (well : raw=List.ofFn (fun j : Fin (D+1)=>encoded e (j.val+1)))
    (i : Fin (D+1)) :
    (readTape he raw i).result=encoded e (i.val+1) ∧
    (readTape he raw i).steps≤(D+1)*(e+2) := by
  subst raw
  let raw := List.ofFn (fun j : Fin (D+1)=>encoded e (j.val+1))
  have hlen : raw.length=D+1 := List.length_ofFn
  have hi : i.val<raw.length := hlen.symm ▸ i.isLt
  obtain ⟨v,t⟩ := scanWord_exact (wordOps e he).toGates raw i.val
  refine ⟨?_,?_⟩
  · simp only [List.getD_eq_getElem?_getD,getElem?_pos raw i.val hi,Option.getD_some] at v
    have eval : raw[i.val]'hi=encoded e (i.val+1) := by
      simp only [raw,List.getElem_ofFn]
    exact v.trans eval
  · change (scanWord (wordOps e he).toGates i.val raw).steps≤_
    simpa only [hlen,wordOps] using t

def generatedProbeBits (f : ℤ[X]) (D n : ℕ) (hN : f.natDegree=n) (fit : D+1<2^f.natDegree) :
    Meter (SuppliedProbeBits (canonicalPrescribed f D fit) n) :=
  let built := positiveTape f.natDegree (D+1)
  let he := positive_width_of_fit f.natDegree D fit
  let load := fun i : Fin (D+1) =>
    let x := readTape he built.result i
    Meter.mk (⟨x.result.val,x.result.property.trans hN⟩ : Word n) x.steps
  have E : ∀ i,(load i).result.val=List.ofFn ((canonicalPrescribed f D fit).word i) := by
    intro i
    have hs := (positive_tape_exact f.natDegree (D+1) he fit).1
    have H := (read_tape_exact f.natDegree D he built.result hs i).1
    change (readTape he built.result i).result.val=List.ofFn (bitAt f.natDegree (i.val+1))
    rw [H,bit_word_exact]
  ⟨⟨load,E⟩,built.steps+3⟩

theorem generated_probe_bits_receipt (f : ℤ[X]) (D n : ℕ)
    (hN : f.natDegree=n) (fit : D+1<2^f.natDegree) :
    let R := generatedProbeBits f D n hN fit
    R.steps=positiveTapeFee f.natDegree (D+1)+3 ∧
    ∀ i : Fin (D+1), (R.result.read i).result.val=encodeBits f.natDegree (i.val+1) ∧
      (R.result.read i).steps≤(D+1)*(f.natDegree+2) := by
  let e := f.natDegree
  let A := positiveTape e (D+1)
  let he := positive_width_of_fit e D fit
  have B := positive_tape_exact e (D+1) he fit
  refine ⟨congrArg (·+3) B.2,?_⟩
  intro i
  have H := read_tape_exact e D he A.result B.1 i
  exact ⟨congrArg Subtype.val H.1,H.2⟩

#print axioms bit_word_exact
#print axioms canonicalPrescribed
#print axioms read_tape_exact
#print axioms generated_probe_bits_receipt
end J6R27PrescribedProbe
