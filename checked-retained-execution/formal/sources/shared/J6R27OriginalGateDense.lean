
import J6R27OriginalGateModeCompare

/-! R17 omitted zero multiplicities in its sparse output. Reinsert them
with a single lockstep scan of the genuine ordered roster and the emitted
support. The equality of full raw keys matters; orientation bits and weights
are not projected away. -/
namespace J6R27OriginalGate
open AOracleMachineTime J6R15ModeCost J6R17ModeTape

def densePush {q : ℕ} (e : Word q) (next : Meter (Option (List (Word q)))) (extra : ℕ) :
    Meter (Option (List (Word q))) :=
  let c := copyFixed e
  ⟨next.result.map (c.result::·),next.steps+c.steps+extra+8⟩

def densify {q : ℕ} : List (RawMode q)→List (RawMode q×Word q)→
    Meter (Option (List (Word q)))
  | [],[] => ⟨some [],4⟩
  | [],_::_ => ⟨none,4⟩
  | _::ms,[] => densePush (word 0) (densify ms []) 0
  | m::ms,s::ss =>
    let test := cmpMode m s.1
    if test.result then densePush s.2 (densify ms ss) test.steps
    else densePush (word 0) (densify ms (s::ss)) test.steps

theorem support_mode_mem {q : ℕ} {ms : List (RawMode q)} {es : List (Word q)}
    {x : RawMode q×Word q} (h : x∈supportSpec ms es) : x.1∈ms := by
  rcases x with ⟨k,e⟩
  exact (List.of_mem_zip (List.mem_filter.mp h).1).1

theorem support_cons_if {q : ℕ} (m : RawMode q) (ms : List (RawMode q))
    (e : Word q) (es : List (Word q)) :
    supportSpec (m::ms) (e::es)=
      if e.val=0 then supportSpec ms es else (m,e)::supportSpec ms es := by
  by_cases e0 : e.val=0 <;> simp [supportSpec,e0]

theorem actual_sparse_to_dense {q : ℕ} (ms : List (RawMode q)) (es : List (Word q))
    (hL : ms.length=es.length) (hN : ms.Nodup) :
    (densify ms (supportSpec ms es)).result=some es := by
  induction ms generalizing es with
  | nil =>
    cases es with
    | nil => rfl
    | cons e es => simp at hL
  | cons m ms ih =>
    cases es with
    | nil => simp at hL
    | cons e es =>
      have hL0 : ms.length=es.length := Nat.succ.inj hL
      have hN0 := List.nodup_cons.mp hN
      have hd := ih es hL0 hN0.2
      rw [support_cons_if]
      by_cases e0 : e.val=0
      · rw [if_pos e0]
        have hz : (word (q:=q) 0)=e := e0 ▸ valued_word e
        cases hS : supportSpec ms es with
        | nil =>
          rw [hS] at hd
          rw [densify,densePush,copy_fixed_exact,hz,hd]
          rfl
        | cons s ss =>
          have miss : m≠s.1 := fun e=> hN0.1 (e ▸ support_mode_mem
            (show s∈supportSpec ms es by rw [hS]; exact List.mem_cons_self))
          rw [hS] at hd
          rw [densify,if_neg (fun u=>miss ((cmp_mode_exact m s.1).1.mp u)),
            densePush,copy_fixed_exact,hz,hd]
          rfl
      · rw [if_neg e0,densify,if_pos ((cmp_mode_exact m m).1.mpr rfl),
          densePush,copy_fixed_exact,hd]
        rfl

def denseRecordFee (a q : ℕ) := 60*a+33*q+40

theorem densify_cost {q : ℕ} (a : ℕ) (ms : List (RawMode q))
    (support : List (RawMode q×Word q))
    (fits : ∀ m∈ms,m.key.1.length≤6*a ∧ m.key.2.length≤6*a) :
    (densify ms support).steps≤4+ms.length*denseRecordFee a q := by
  induction ms generalizing support with
  | nil => cases support <;> simp [densify]
  | cons m ms ih =>
    have F (x : RawMode q) (hx : x∈ms) := fits x (List.mem_cons_of_mem _ hx)
    have fm := fits m List.mem_cons_self
    cases support with
    | nil =>
      have B := ih [] F
      simp only [densify,densePush,copy_fixed_exact,List.length_cons,Nat.add_mul,one_mul]
      unfold denseRecordFee at B ⊢
      omega
    | cons s ss =>
      have C := (cmp_mode_exact m s.1).2
      by_cases hit : (cmpMode m s.1).result=true
      · have B := ih ss F
        simp only [densify,hit,if_true,densePush,copy_fixed_exact,List.length_cons,Nat.add_mul,one_mul]
        unfold denseRecordFee at B ⊢
        omega
      · have B := ih (s::ss) F
        rw [densify,if_neg hit]
        simp only [densePush,copy_fixed_exact,List.length_cons,Nat.add_mul,one_mul]
        unfold denseRecordFee at B ⊢
        omega

def dispatchDense {q : ℕ} (a : ℕ) (T : RawTape q)
    (exponents : List (Word q)) : Meter (Option (List (Word q))) :=
  let S := emitSupport a T.modes exponents
  match S.result with
  | none => ⟨none,S.steps+4⟩
  | some sp =>
    let U := densify T.modes sp
    ⟨U.result,S.steps+U.steps+4⟩

theorem dispatch_dense_exact {q : ℕ} (a : ℕ) (T : RawTape q) (es : List (Word q))
    (hL : T.modes.length=es.length) (hN : T.modes.Nodup)
    (fits : ∀ m∈T.modes,m.key.1.length≤6*a ∧ m.key.2.length≤6*a) :
    let out := dispatchDense a T es
    out.result=some es ∧
      out.steps≤12+T.modes.length*(dispatchStride a q+denseRecordFee a q) := by
  obtain ⟨hr,hc⟩ := emitSupport_exact a T.modes es hL
  have eq := actual_sparse_to_dense T.modes es hL hN
  have fee := densify_cost a T.modes (supportSpec T.modes es) fits
  unfold dispatchDense
  dsimp only
  rw [hr]
  simp only [eq,hc,true_and,Nat.mul_add]
  omega

#print axioms support_mode_mem
#print axioms actual_sparse_to_dense
#print axioms densify_cost
#print axioms dispatch_dense_exact
end J6R27OriginalGate


