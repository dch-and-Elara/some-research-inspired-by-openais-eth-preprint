import J6R51DispatchLegacy
import J6R49DFSCentreBase

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 2500

/-! Read the ordinal of the actual chosen binary probe. The paper's
chosenRep is not assumed to be a numeral encoding. Instead read the
measured mask file, copying every literal as it is written. -/
namespace J6R52Dispatch
open scoped Polynomial Classical
open AOracleMachineTime J6R15ModeCost J6R27OriginalGate J6R51Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R49DFS
open J6R24MeteredRecursion J1PPrinted

theorem word_eq_of_bits {q : ℕ} {x y : Word q} (h : x.bits=y.bits) : x=y := by
  rcases x with ⟨xb,hx⟩
  rcases y with ⟨yb,hy⟩
  change xb=yb at h
  subst yb
  rfl

noncomputable def probeCode (e n : ℕ) (fit : n≤2^e) (z : Fin n) : Word e :=
  ⟨List.ofFn (NativeProbeRing.chosenRep e n fit z),List.length_ofFn⟩

theorem probe_code_injective (e n : ℕ) (fit : n≤2^e) :
    Function.Injective (probeCode e n fit) := by
  intro x y h
  have b := congrArg Word.bits h
  apply NativeProbeRing.chosenRep_injective _ _ fit
  exact List.ofFn_inj.mp b

def probeKeyFile {n e : ℕ} (masks : Fin n→Meter {w : List Bool // w.length=e}) :
    List (Fin n)→Meter (List (List (Word e)))
  | [] => ⟨[],3⟩
  | z::zs =>
    let mask := masks z
    let write := copyFixed (⟨mask.result.val,mask.result.property⟩ : Word e)
    let out := probeKeyFile masks zs
    ⟨[write.result]::out.result,mask.steps+write.steps+out.steps+6⟩

theorem probe_key_file_exact {n e : ℕ}
    (masks : Fin n→Meter {w : List Bool // w.length=e})
    (fit : n≤2^e) (correct : ∀ z, (masks z).result.val=(probeCode e n fit z).bits)
    (roster : List (Fin n)) :
    probeKeyFile masks roster =
      ⟨roster.map (fun z=>[probeCode e n fit z]),
        3+(roster.map (fun z=>(masks z).steps+3*e+7)).sum⟩ := by
  induction roster with
  | nil => rfl
  | cons z rest ih =>
    have w : (⟨(masks z).result.val,(masks z).result.property⟩ : Word e)=probeCode e n fit z := word_eq_of_bits (correct z)
    simp only [probeKeyFile,copy_fixed_exact,ih,w,List.map_cons,List.sum_cons]
    congr 1
    omega

def readProbeOrdinal {n e tz : ℕ}
    (masks : Fin n→Meter {w : List Bool // w.length=e}) (current : Word e) :
    Meter (Option (Word tz)) :=
  let file := probeKeyFile masks (List.finRange n)
  let z := readPriorOrdinal (tm:=tz) [current] file.result
  ⟨z.result,file.steps+z.steps+4⟩

theorem actual_binary_probe_ordinal {n e tz : ℕ}
    (masks : Fin n→Meter {w : List Bool // w.length=e})
    (fit : n≤2^e) (correct : ∀ z, (masks z).result.val=(probeCode e n fit z).bits)
    (z : Fin n) (current : Word e) (same : current.bits=(probeCode e n fit z).bits)
    (ht : 0<tz) (room : n<2^tz) :
    let out := readProbeOrdinal (tz:=tz) masks current
    out.result=some (word z.val) ∧ (word (q:=tz) z.val).val=z.val ∧
      out.steps ≤ (3+((List.finRange n).map (fun j=>(masks j).steps+3*e+7)).sum)+
        (3*tz+7+n*(10*e+9+13*tz+12))+4 := by
  let encode := fun x=>[probeCode e n fit x]
  have eCurrent : current=probeCode e n fit z := word_eq_of_bits same
  have inj : Function.Injective encode := by
    intro x y h
    exact probe_code_injective e n fit (List.cons.inj h).1
  have mem : [current]∈(List.finRange n).map encode := by
    rw [eCurrent]
    exact List.mem_map_of_mem (f:=encode) (List.mem_finRange z)
  have find : ((List.finRange n).map encode).idxOf [current]=z.val := by
    rw [eCurrent]
    refine (idx_of_real_beq_encoding encode inj z (List.finRange n)).trans ?_
    exact List.idxOf_finRange z
  have fl : ((List.finRange n).map encode).length=n := by simp
  have h := read_prior_ordinal_correct (tm:=tz) [current] ((List.finRange n).map encode)
    ht (by rw [fl]; exact room) mem
  obtain ⟨result,fee⟩ := h
  rw [find] at result
  rw [fl] at fee
  unfold readProbeOrdinal
  dsimp only
  rw [probe_key_file_exact masks fit correct]
  dsimp only
  refine ⟨result,word_val (z.isLt.trans room),?_⟩
  change (3+((List.finRange n).map (fun j=>(masks j).steps+3*e+7)).sum)+
    (readPriorOrdinal (tm:=tz) [current] ((List.finRange n).map encode)).steps+4≤_
  simp only [List.length_singleton,one_mul] at fee
  omega

#print axioms probe_code_injective
#print axioms probe_key_file_exact
#print axioms actual_binary_probe_ordinal
end J6R52Dispatch

