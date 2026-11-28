import J4R43LiteralOutsideUnitWord

/-! Fixed-width bytecode for the scalar part of one outside register.
Every source read or constant copy has a bill, and every arithmetic
node calls the verified p-bit word kernel. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open A1R10 A1R12 AOracleMachineTime AOracleCoordinates
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4300000

inductive ScalarCode where
  | flag : Bool→ScalarCode
  | unit : ScalarCode
  | add : ScalarCode→ScalarCode→ScalarCode
  | mul : ScalarCode→ScalarCode→ScalarCode
  | sub : ScalarCode→ScalarCode→ScalarCode

def ScalarCode.size : ScalarCode→ℕ
  | .flag _ | .unit => 1
  | .add x y | .mul x y | .sub x y => x.size+y.size+1

def ScalarCode.denote {R : Type} [CommRing R] (κ : R) : ScalarCode→R
  | .flag b => if b then 1 else 0
  | .unit => κ
  | .add x y => x.denote κ+y.denote κ
  | .mul x y => x.denote κ*y.denote κ
  | .sub x y => x.denote κ-y.denote κ

def codeStride (p : ℕ) : ℕ := wordOpCap p+5*p+10

def runScalarCode {p : ℕ} (hp : 0<p) (κ : Word p) : ScalarCode→Meter (Word p)
  | .flag b => ⟨if b then wordOne p else wordZero p,3*p+4⟩
  | .unit => ⟨κ,p+2⟩
  | .add x y =>
    let X := runScalarCode hp κ x
    let Y := runScalarCode hp κ y
    let r := addWord X.result Y.result
    ⟨r.result,X.steps+Y.steps+r.steps+5*p+10⟩
  | .mul x y =>
    let X := runScalarCode hp κ x
    let Y := runScalarCode hp κ y
    let r := mulWord X.result Y.result
    ⟨r.result,X.steps+Y.steps+r.steps+5*p+10⟩
  | .sub x y =>
    let X := runScalarCode hp κ x
    let Y := runScalarCode hp κ y
    let r := subWord hp X.result Y.result
    ⟨r.result,X.steps+Y.steps+r.steps+5*p+10⟩

theorem actual_code_read {p : ℕ} (hp : 0<p) (κ : Word p) (c : ScalarCode) :
    wordRead (runScalarCode hp κ c).result=c.denote (wordRead κ) := by
  induction c with
  | flag b =>
    cases b
    · exact (wordOps p hp).zero_read
    · exact wordOne_read p hp
  | unit => rfl
  | add x y X Y => simp only [runScalarCode,addWord_read,ScalarCode.denote,X,Y]
  | mul x y X Y => simp only [runScalarCode,mulWord_read,ScalarCode.denote,X,Y]
  | sub x y X Y => simp only [runScalarCode,subWord_read,ScalarCode.denote,X,Y]

theorem actual_code_cost {p : ℕ} (hp : 0<p) (κ : Word p) (c : ScalarCode) :
    (runScalarCode hp κ c).steps≤c.size*codeStride p := by
  induction c with
  | flag b =>
    unfold codeStride
    change 3*p+4≤_
    simp only [ScalarCode.size,one_mul]
    omega
  | unit =>
    unfold codeStride
    change p+2≤_
    simp only [ScalarCode.size,one_mul]
    omega
  | add x y X Y =>
    let a := runScalarCode hp κ x
    let b := runScalarCode hp κ y
    have r : (addWord a.result b.result).steps≤wordOpCap p := (wordOps p hp).add_cost _ _
    have X' : a.steps≤x.size*codeStride p := X
    have Y' : b.steps≤y.size*codeStride p := Y
    change a.steps+b.steps+(addWord a.result b.result).steps+5*p+10≤(x.size+y.size+1)*codeStride p
    simp only [Nat.add_mul,one_mul]
    have h : wordOpCap p+5*p+10=codeStride p := rfl
    omega
  | mul x y X Y =>
    let a := runScalarCode hp κ x
    let b := runScalarCode hp κ y
    have r : (mulWord a.result b.result).steps≤wordOpCap p := (wordOps p hp).mul_cost _ _
    have X' : a.steps≤x.size*codeStride p := X
    have Y' : b.steps≤y.size*codeStride p := Y
    change a.steps+b.steps+(mulWord a.result b.result).steps+5*p+10≤(x.size+y.size+1)*codeStride p
    simp only [Nat.add_mul,one_mul]
    have h : wordOpCap p+5*p+10=codeStride p := rfl
    omega
  | sub x y X Y =>
    let a := runScalarCode hp κ x
    let b := runScalarCode hp κ y
    have r : (subWord hp a.result b.result).steps≤wordOpCap p := (wordOps p hp).sub_cost _ _
    have X' : a.steps≤x.size*codeStride p := X
    have Y' : b.steps≤y.size*codeStride p := Y
    change a.steps+b.steps+(subWord hp a.result b.result).steps+5*p+10≤(x.size+y.size+1)*codeStride p
    simp only [Nat.add_mul,one_mul]
    have h : wordOpCap p+5*p+10=codeStride p := rfl
    omega

#print axioms actual_code_read
#print axioms actual_code_cost
end
end J4R43LiteralOutside

