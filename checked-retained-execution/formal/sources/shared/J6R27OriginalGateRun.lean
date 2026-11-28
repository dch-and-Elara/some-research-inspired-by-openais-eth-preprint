
import J6R27OriginalGateCompile

/-! The paid compiler preserves the actual source gate opcode and sign
bits. Its emitted ordinal words are consumed by an executable reader,
rather than replaced by the reference implementation's math indices. -/
namespace J6R27OriginalGate
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R10Repack
open J6R21Ancestor J6R21Leaf J6OrientedHost

inductive CodeGate (A : Type*) where
  | clause (port : List A) (sign : List Bool)
  | equal (port : List A)
  | free

def encodeGate {A : Type*} {d : ℕ} (port : Fin d→A) : Gate d→CodeGate A
  | .clause sign => .clause (List.ofFn port) (List.ofFn sign)
  | .equal => .equal (List.ofFn port)
  | .free => .free

def compileGate {w : ℕ} (b : ℕ) (marks : List Bool) (rows : List (Word (w+marks.length))) :
    CodeGate (OriginSeed w) → Meter (Option (CodeGate (Word b)))
  | .free => ⟨some .free,2⟩
  | .clause ports signs =>
    let out := compileIncidences b marks rows ports
    let copy := copyBytes signs
    ⟨out.result.map (fun p=>.clause p copy.result),out.steps+copy.steps+4⟩
  | .equal ports =>
    let out := compileIncidences b marks rows ports
    ⟨out.result.map CodeGate.equal,out.steps+4⟩

def gateBuildCap (w b depth n d : ℕ) := 8+d*(seekCap w b depth n+b+9)

variable {f : ℤ[X]} {ell w n : ℕ} {root cur : Point f ell}

theorem compile_gate_exact {b d : ℕ} (hb : 0<b)
    (code : root.host.Edge→Word w) (hc : Function.Injective code)
    (tr : Trace root cur) (ord : Fin n≃cur.host.Edge) (marks : List Bool)
    (hd : marks.length=tr.depth) (fit : n≤2^b) (scope : Fin d→PortAt root) (gate : Gate d)
    (rows : List (Word (w+marks.length)))
    (actual : rows=List.ofFn (indexedKeys code tr ord marks hd)) :
    let out := compileGate b marks rows (encodeGate (seedFrom code ∘ scope) gate)
    out.result=some (encodeGate (fun j=>word (tracedSlot tr ord (scope j)).val) gate) ∧
    out.steps≤gateBuildCap w b marks.length n d := by
  let src := List.ofFn (seedFrom code ∘ scope)
  let dst := List.ofFn (fun j=>word (q:=b) (tracedSlot tr ord (scope j)).val)
  have H := compile_actual_traced_ordinals hb code hc tr ord marks hd fit (List.ofFn scope) rows actual
  have hv : (compileIncidences b marks rows src).result=some dst := by
    simpa only [List.map_ofFn,Function.comp_def] using H.1
  have hp : (compileIncidences b marks rows src).steps≤3+d*(seekCap w b marks.length n+b+6) := by
    simpa only [List.map_ofFn,Function.comp_def,List.length_ofFn] using H.2
  have hmon := Nat.mul_le_mul_left d (show seekCap w b marks.length n+b+6≤
    seekCap w b marks.length n+b+9 by omega)
  cases gate with
  | free =>
    exact ⟨rfl,by change 2≤8+_; omega⟩
  | equal =>
    refine ⟨?_,?_⟩
    · change (compileIncidences b marks rows src).result.map CodeGate.equal=some (.equal dst)
      rw [hv]
      rfl
    · change (compileIncidences b marks rows src).steps+4≤gateBuildCap _ _ _ _ _
      unfold gateBuildCap
      omega
  | clause signs =>
    refine ⟨?_,?_⟩
    · change (compileIncidences b marks rows src).result.map
        (fun p=>CodeGate.clause p (copyBytes (List.ofFn signs)).result)=some (.clause dst (List.ofFn signs))
      rw [hv,copyBytes_exact]
      rfl
    · change (compileIncidences b marks rows src).steps+(copyBytes (List.ofFn signs)).steps+4≤_
      rw [copyBytes_exact]
      simp only [List.length_ofFn,gateBuildCap]
      rw [Nat.mul_add d (seekCap w b marks.length n+b) 6] at hp
      rw [Nat.mul_add d (seekCap w b marks.length n+b) 9]
      omega

def readCode {b : ℕ} (bits : List Bool) (addr : Word b) : Meter Bool :=
  let out := A1R9.seekBlock (fun _=>1) addr.bits bits
  ⟨out.result.getD false,out.steps+addr.bits.length+3⟩

def readCodes {b : ℕ} (bits : List Bool) : List (Word b)→Meter (List Bool)
  | [] => ⟨[],1⟩
  | x::xs =>
    let m := readCode bits x
    let out := readCodes bits xs
    ⟨m.result::out.result,m.steps+out.steps+2⟩

def runCode {b : ℕ} (bits : List Bool) : CodeGate (Word b)→Meter Bool
  | .free => ⟨true,2⟩
  | .clause ports signs =>
    let r := readCodes bits ports
    ⟨(List.zipWith (· == ·) r.result signs).any id,r.steps+5*ports.length+4⟩
  | .equal ports =>
    let r := readCodes bits ports
    ⟨localAllEqual r.result,r.steps+5*ports.length+4⟩

def forgetBit {n b : ℕ} (a : BitAddress n b) : Word b := ⟨a.code.val,a.code.property⟩

def forgetGate {n b : ℕ} : OriginalGateTape n b→CodeGate (Word b)
  | .free => .free
  | .clause p s => .clause (p.map forgetBit) s
  | .equal p => .equal (p.map forgetBit)

theorem coded_scan_is_original {n b : ℕ} (bits : List Bool) (xs : List (BitAddress n b)) :
    readCodes bits (xs.map forgetBit)=scanWords bits xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,readCodes,scanWords,ih]
    rfl

theorem coded_run_is_original {n b : ℕ} (bits : List Bool) (g : OriginalGateTape n b) :
    runCode bits (forgetGate g)=runOriginalGate bits g := by
  cases g <;> simp only [forgetGate,runCode,runOriginalGate,coded_scan_is_original,List.length_map]

theorem exact_code_is_forgotten {b d : ℕ} (fit : n≤2^b) (port : Fin d→Fin n) (g : Gate d) :
    encodeGate (fun j=>word (q:=b) (port j).val) g=forgetGate (gateTape fit port g) := by
  cases g <;> simp only [encodeGate,forgetGate,gateTape,List.map_ofFn] <;> rfl

#print axioms compile_gate_exact
#print axioms coded_scan_is_original
#print axioms coded_run_is_original
#print axioms exact_code_is_forgotten
end J6R27OriginalGate


