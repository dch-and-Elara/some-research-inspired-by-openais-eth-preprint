import AOracleMachineTimeTape
import AOracleMachineTimeMul

/-!
# Compact original gates and sparse local forms as bit programs

Every original incidence and sparse linear term uses a bit-coded
address. The implementation actually scans a supplied assignment tape;
it does not regard a compressed table or the entire assignment as one
read. Coefficient words are literal fixed-size scalar records here.
-/

namespace AOracleMachineTimeLocal
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul AOracleSuccinct

def readPorts (assignment : List Bool) : List (List Bool) → Meter (List Bool)
  | [] => ⟨[],0⟩
  | addr :: addresses =>
    let x := seek addr assignment
    let rest := readPorts assignment addresses
    ⟨x.result.getD false :: rest.result,x.steps+rest.steps+2⟩

theorem readPorts_exact {n : ℕ} (a : Fin n → Bool) (ports : List (Fin n)) (b : ℕ)
    (hfit : n≤2^b) :
    (readPorts (List.ofFn a) (ports.map (fun j => encodeBits b j.val))).result=ports.map a ∧
    (readPorts (List.ofFn a) (ports.map (fun j => encodeBits b j.val))).steps ≤
      ports.length*((10*b+4)*n+2) := by
  induction ports with
  | nil => simp [readPorts]
  | cons j ports ih =>
    obtain ⟨hr,hc⟩ := ih
    have h := encoded_seek b j.val (j.isLt.trans_le hfit) (List.ofFn a)
    have hd : (seek (encodeBits b j.val) (List.ofFn a)).result=some (a j) := by
      rw [h.1]
      simp [j.isLt]
    simp only [List.map_cons, readPorts, hd, hr, List.length_cons]
    refine ⟨rfl,?_⟩
    have hb : (seek (encodeBits b j.val) (List.ofFn a)).steps≤(10*b+4)*n := by
      simpa using h.2
    rw [Nat.add_mul, one_mul]
    omega

theorem rank_is_tape_value {n : ℕ} (a : Fin n → Bool) :
    bitsValue (List.ofFn a)=rankBits a := by
  induction n with
  | zero => simp [rankBits, bitsValue]
  | succ n ih =>
    rw [List.ofFn_succ, bitsValue, ih, rankBits]

def readTensor (ports : List (List Bool)) (table assignment : List Bool) : Meter Bool :=
  let addr := readPorts assignment ports
  let out := seek addr.result table
  ⟨out.result.getD false,addr.steps+out.steps+2⟩

/-- A genuine local vertex lookup on two physical bit tapes. -/
theorem readTensor_exact {n delta : ℕ} (T : BoolTensor n delta)
    (a : Fin n → Bool) (b : ℕ) (hfit : n≤2^b) :
    let run := readTensor ((List.ofFn T.port).map (fun j => encodeBits b j.val))
      (List.ofFn T.table) (List.ofFn a)
    run.result=T.read a ∧ run.steps≤
      T.arity*((10*b+4)*n+2)+(10*T.arity+4)*2^T.arity+2 := by
  let ports := ((List.ofFn T.port).map (fun j => encodeBits b j.val))
  have h := readPorts_exact a (List.ofFn T.port) b hfit
  have hl : (readPorts (List.ofFn a) ports).result=List.ofFn (fun j => a (T.port j)) := by
    simpa only [ports, List.map_ofFn] using h.1
  have hc : (readPorts (List.ofFn a) ports).steps≤T.arity*((10*b+4)*n+2) := by
    simpa only [ports,List.length_ofFn] using h.2
  have ht := seek_exact (List.ofFn (fun j => a (T.port j))) (List.ofFn T.table)
  have he : (seek (List.ofFn (fun j => a (T.port j))) (List.ofFn T.table)).result=some (T.read a) := by
    rw [ht.1,rank_is_tape_value]
    simp [BoolTensor.read,rankBits_lt]
  have hh : (seek (List.ofFn (fun j => a (T.port j))) (List.ofFn T.table)).steps≤
      (10*T.arity+4)*2^T.arity := by
    simpa only [List.length_ofFn] using ht.2
  change (readTensor ports (List.ofFn T.table) (List.ofFn a)).result=T.read a ∧
    (readTensor ports (List.ofFn T.table) (List.ofFn a)).steps≤_
  unfold readTensor
  dsimp only
  rw [hl,he]
  exact ⟨rfl,by omega⟩

/-- A supplied scalar residue written at its canonical p-bit width. -/
def residueWord (p : ℕ) (x : ZMod (2^p)) : List Bool :=
  encodeBits p x.val

theorem residueWord_length (p : ℕ) (x : ZMod (2^p)) : (residueWord p x).length=p :=
  encodeBits_length p x.val

theorem residueWord_correct (p : ℕ) (x : ZMod (2^p)) :
    asResidue p (residueWord p x)=x := by
  haveI : NeZero ((2:ℕ)^p) := ⟨by positivity⟩
  unfold residueWord asResidue
  rw [encodeBits_exact p x.val (ZMod.val_lt x)]
  exact ZMod.natCast_zmod_val x

/-- At each sparse entry, visit its address on the column assignment
tape, then do one modular ripple addition or no addition. -/
def runLinear (p : ℕ) (assignment : List Bool) :
    List (List Bool × List Bool) → Meter (List Bool)
  | [] => ⟨List.replicate p false,p⟩
  | (addr,c) :: entries =>
    let bit := seek addr assignment
    let rest := runLinear p assignment entries
    let out := if bit.result.getD false then addBits c rest.result else Meter.pure rest.result
    ⟨out.result,bit.steps+rest.steps+out.steps+4⟩

def packLinear {n : ℕ} (b p : ℕ) (es : Linear n (ZMod (2^p))) :
    List (List Bool × List Bool) :=
  es.map (fun jw => (encodeBits b jw.1.val,residueWord p jw.2))

/-- One chosen sparse local form or source moment is bitwise exact,
with each original column read and all modular additions charged. -/
theorem runLinear_exact {n : ℕ} (a : Fin n → Bool) (b p : ℕ)
    (es : Linear n (ZMod (2^p))) (hfit : n≤2^b) :
    let q := runLinear p (List.ofFn a) (packLinear b p es)
    q.result.length=p ∧ asResidue p q.result=linearEval a es ∧
      q.steps≤p+es.length*((10*b+4)*n+12*p+4) := by
  induction es with
  | nil => simp [packLinear,runLinear, value_zero, asResidue, linearEval]
  | cons e es ih =>
    rcases e with ⟨j,w⟩
    obtain ⟨hl,hv,hc⟩ := ih
    have s := encoded_seek b j.val (j.isLt.trans_le hfit) (List.ofFn a)
    have hread : (seek (encodeBits b j.val) (List.ofFn a)).result=some (a j) := by
      rw [s.1]
      simp [j.isLt]
    have htime : (seek (encodeBits b j.val) (List.ofFn a)).steps≤(10*b+4)*n := by
      simpa only [List.length_ofFn] using s.2
    generalize hrest : runLinear p (List.ofFn a) (packLinear b p es) = v at hl hv hc ⊢
    have hw := residueWord_length p w
    have hstep := addBits_exact (residueWord p w) v.result (hw.trans hl.symm)
    have hh := add_residue p (residueWord p w) v.result hw hl
    have hr : asResidue p (residueWord p w)=w := residueWord_correct _ _
    rw [show packLinear b p ((j,w)::es) =
      (encodeBits b j.val,residueWord p w)::packLinear b p es by rfl]
    rw [runLinear, hrest]
    dsimp only
    rw [hread]
    cases ha : a j
    · simp only [ha, Option.getD_some, Bool.false_eq_true, if_false, Meter.pure,
        linearEval, zero_add, List.length_cons]
      refine ⟨hl,hv,?_⟩
      rw [Nat.add_mul, one_mul]
      omega
    · simp only [ha, Option.getD_some, if_true, linearEval, List.length_cons]
      refine ⟨hstep.1.trans hw, by rw [hh,hr,hv],?_⟩
      rw [hstep.2.2, hw, Nat.add_mul, one_mul]
      omega

#print axioms readPorts_exact
#print axioms readTensor_exact
#print axioms residueWord_correct
#print axioms runLinear_exact

end AOracleMachineTimeLocal

