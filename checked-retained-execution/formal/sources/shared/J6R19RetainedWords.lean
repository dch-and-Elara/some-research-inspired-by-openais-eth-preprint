import A1R12Words
import A1R12Table

/-! A retained entry's least residue words are resized as unsigned
integers. Nothing here re-evaluates an old description or computes
an incidence oracle. Truncation and zero extension are real scans. -/
namespace J6R19Retained
open A1R10 A1R11 A1R12 AOracleMachineTime AOracleMachineTimeMul

def scanWidth : ℕ → List Bool → Meter (List Bool)
  | 0,_ => ⟨[],1⟩
  | q+1,[] =>
    let h := scanWidth q []
    ⟨false::h.result,h.steps+4⟩
  | q+1,b::bs =>
    let h := scanWidth q bs
    ⟨b::h.result,h.steps+4⟩

theorem scanWidth_exact (q : ℕ) (l : List Bool) :
    (scanWidth q l).result=lowBits q l ∧ (scanWidth q l).steps=4*q+1 := by
  induction q generalizing l with
  | zero => simp [scanWidth,lowBits]
  | succ q ih =>
    cases l <;> simp [scanWidth,lowBits,ih] <;> omega

def resizeWord {p : ℕ} (q : ℕ) (v : Word p) : Meter (Word q) :=
  let z := scanWidth q v.val
  ⟨⟨z.result,(congrArg List.length (scanWidth_exact q v.val).1).trans (lowBits_len q v.val)⟩,
    z.steps+2*p+4⟩

def wordFee (p q : ℕ) := 2*p+4*q+5

theorem wordLeast {p : ℕ} (v : Word p) : (wordRead v).val=bitsValue v.val := by
  change ((bitsValue v.val:ZMod (2^p))).val=bitsValue v.val
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by simpa only [v.property] using bitsValue_lt v.val)]

theorem resizeWord_exact {p : ℕ} (q : ℕ) (v : Word p) :
    wordRead (resizeWord q v).result=((wordRead v).val:ZMod (2^q)) ∧
      (resizeWord q v).steps=wordFee p q := by
  have h := scanWidth_exact q v.val
  constructor
  · change (bitsValue (scanWidth q v.val).result:ZMod (2^q))=_
    rw [h.1,lowBits_value,ZMod.natCast_mod,wordLeast]
  · change (scanWidth q v.val).steps+2*p+4=_
    rw [h.2,wordFee]
    omega

def resizeU {p q : ℕ} {old : List (Word p)} {new : List (Word q)}
    (h : old.length=new.length) (v : UBlock old) : Meter (UBlock new) :=
  let z := A1R12.mapMeter (resizeWord q) q v.val
  have hh := A1R12.mapMeter_exact (resizeWord q) q (wordFee p q) v.val
    (fun t _ => (resizeWord_exact q t).2.le)
  ⟨⟨z.result,(congrArg List.length hh.1).trans (by rw [List.length_map,v.property,h])⟩,z.steps⟩

def scalarFee (e p q : ℕ) := e*(wordFee p q+q+4)

theorem resizeU_exact {p q : ℕ} {old : List (Word p)} {new : List (Word q)}
    (h : old.length=new.length) (v : UBlock old) :
    (resizeU h v).result.val=v.val.map (fun w=>(resizeWord q w).result) ∧
      (resizeU h v).steps≤scalarFee old.length p q := by
  obtain ⟨hA,hB⟩ := A1R12.mapMeter_exact (resizeWord q) q (wordFee p q) v.val
    (fun t _ => (resizeWord_exact q t).2.le)
  refine ⟨hA,?_⟩
  simpa only [resizeU,scalarFee,v.property] using hB

def resizeUV {p q ell : ℕ} {old : List (Word p)} {new : List (Word q)}
    (h : old.length=new.length) (v : UVBlock old ell) : Meter (UVBlock new ell) :=
  let z := A1R12.mapMeter (resizeU h) (new.length*q) v.val
  have hh := A1R12.mapMeter_exact (resizeU h) (new.length*q) (scalarFee old.length p q) v.val
    (fun t _ => (resizeU_exact h t).2)
  ⟨⟨z.result,(congrArg List.length hh.1).trans (by rw [List.length_map,v.property])⟩,z.steps⟩

def boxFee (e ell p q : ℕ) := ell*(scalarFee e p q+e*q+4)

theorem resizeUV_exact {p q ell : ℕ} {old : List (Word p)} {new : List (Word q)}
    (h : old.length=new.length) (v : UVBlock old ell) :
    (resizeUV h v).result.val=v.val.map (fun w=>(resizeU h w).result) ∧
      (resizeUV h v).steps≤boxFee old.length ell p q := by
  obtain ⟨hA,hB⟩ := A1R12.mapMeter_exact (resizeU h) (new.length*q) (scalarFee old.length p q) v.val
    (fun t _ => (resizeU_exact h t).2)
  refine ⟨hA,?_⟩
  simpa only [resizeUV,boxFee,v.property,h] using hB

#print axioms scanWidth_exact
#print axioms wordLeast
#print axioms resizeWord_exact
#print axioms resizeU_exact
#print axioms resizeUV_exact
end J6R19Retained


