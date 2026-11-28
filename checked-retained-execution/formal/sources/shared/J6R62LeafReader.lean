import J6R50LeafOnline

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3500

/-! Price the exact R53 terminal's typed ReadCmd list by its real syntax
and the real fetched atlas. No evaluation callback cost is supplied. -/
namespace J6R62Leaf
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Leaf J6R27OriginalGate
open J6R48Leaf J6R50Leaf J6R33StatefulArithmeticPage J6R22Active
open A1R10 A1R11 A1R12

theorem sum_map_cap {V : Type*} (xs : List V) (fee : V → ℕ) (cap : ℕ)
    (h : ∀ u∈xs, fee u ≤ cap) : (xs.map fee).sum ≤ xs.length*cap := by
  induction xs with
  | nil => simp
  | cons u us ih =>
    exact (Nat.add_le_add (h u List.mem_cons_self)
      (ih (fun v hv=>h v (List.mem_cons_of_mem _ hv)))).trans_eq
      (by simp only [List.length_cons,Nat.add_mul,one_mul]; omega)

def gatePorts {A : Type} : CodeGate A → ℕ
  | .free => 0
  | .equal ks => ks.length
  | .clause ks _ => ks.length

theorem raw_code_word_fee {b : ℕ} (bits : List Bool) (u : J6R15ModeCost.Word b) :
    (readCode bits u).steps ≤ addressFee bits.length b := by
  have a := (A1R9.seekBlock_exact (fun _ : Bool => 1) u.bits bits).2
  have s := sum_map_cap bits (fun _=>1) 1 (fun _ _=>le_rfl)
  simp only [u.size,mul_one] at a s
  change (A1R9.seekBlock _ u.bits bits).steps+u.bits.length+3≤_
  rw [u.size,addressFee]
  have h : (10*b+5)*bits.length=(10*b+4)*bits.length+bits.length := by ring
  omega

theorem raw_code_words_fee {b : ℕ} (bits : List Bool) (ports : List (J6R15ModeCost.Word b)) :
    (readCodes bits ports).steps ≤ 1+ports.length*(addressFee bits.length b+2) := by
  induction ports with
  | nil => simp [readCodes]
  | cons u us ih =>
    have h := raw_code_word_fee bits u
    simp only [readCodes,List.length_cons,Nat.add_mul,one_mul]
    omega

theorem raw_code_gate_fee {b : ℕ} (bits : List Bool) (g : CodeGate (J6R15ModeCost.Word b)) :
    (runCode bits g).steps ≤ originalGateFee bits.length b (gatePorts g) := by
  cases g with
  | free => simp [runCode,originalGateFee,gatePorts]
  | equal ks =>
    have h := raw_code_words_fee bits ks
    simp only [runCode,originalGateFee,gatePorts,Nat.mul_add] at h ⊢
    have e : 5*ks.length=ks.length*5 := mul_comm _ _
    omega
  | clause ks signs =>
    have h := raw_code_words_fee bits ks
    simp only [runCode,originalGateFee,gatePorts,Nat.mul_add] at h ⊢
    have e : 5*ks.length=ks.length*5 := mul_comm _ _
    omega

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "Bank" => PageBank f ell key prec tw bw page

def ReadFormat (B : Bank) (N : ℕ) (cmd : ReadCmd key page) : Prop :=
  match cmd with
  | .gate _ _ => True
  | .packet id pg d wires => ResidentReadForm B (PageReadCode.generated (edges:=N) id pg d wires)

def readCmdFee (B : Bank) (e p N : ℕ) (cmd : ReadCmd key page) : ℕ :=
  match cmd with
  | .gate b g => originalGateFee N b (gatePorts g)+uvWidth e ell p+4
  | .packet id pg d wires => rawPageFee e p N B (PageReadCode.generated (edges:=N) id pg d wires)

theorem literal_read_cmd_upper {p N : ℕ} (hf : f.Monic)
    (F : J6R24MeteredRecursion.Frame f p) (ellPos : 0<ell)
    (B : Bank) (cmd : ReadCmd key page) (fit : ReadFormat B N cmd)
    (bits : List Bool) (size : bits.length=N) :
    (cmd.read hf F ellPos B bits).steps ≤ readCmdFee B F.words.length p N cmd := by
  cases cmd with
  | gate b g =>
    have h := raw_code_gate_fee bits g
    rw [size] at h
    exact Nat.add_le_add_right (Nat.add_le_add_right h _) _
  | packet id pg d wires =>
    exact raw_paged_read_bound hf F ellPos B (.generated id pg d wires)
      fit bits size

def cmdBill (B : Bank) (e p N : ℕ) (cmds : List (ReadCmd key page)) : ℕ :=
  (cmds.map (readCmdFee B e p N)).sum

theorem same_row_interpreter_fee {p N : ℕ} (hf : f.Monic)
    (F : J6R24MeteredRecursion.Frame f p) (ellPos : 0<ell)
    (B : Bank) (clk : List Unit) (clock : clk.length=N) (cmds : List (ReadCmd key page))
    (fit : ∀ t∈cmds, ReadFormat B N t) :
    (runRows hf F ellPos B clk cmds).steps ≤
      rawLeafCap F.words.length ell p N cmds.length (cmdBill B F.words.length p N cmds) F.hp := by
  unfold runRows
  rw [clocked_leaf_is_native_enumerator F.hp F.sizePos ellPos cmds _ clk clock]
  have h := (leafCompute_bills_every_entry F.hp F.sizePos ellPos N cmds
    (fun t=>t.read hf F ellPos B)).2
  have row (bits : Fin N → Bool) (cs : List (ReadCmd key page))
      (forms : ∀ t∈cs, ReadFormat B N t) :
      thisVertexBill cs (fun t=>t.read hf F ellPos B) (List.ofFn bits) ≤
        cmdBill B F.words.length p N cs := by
    unfold thisVertexBill cmdBill
    induction cs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add
        (literal_read_cmd_upper hf F ellPos B x (forms x List.mem_cons_self) _ List.length_ofFn)
        (ih (fun y hy => forms y (List.mem_cons_of_mem _ hy)))
  have checked : leafEntryBill N cmds (fun t=>t.read hf F ellPos B) ≤
      2^N*cmdBill B F.words.length p N cmds := by
    have hm := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin N→Bool)))
      (fun x _=>row x cmds fit)
    have hc : Fintype.card (Fin N→Bool)=2^N := by simp
    simpa only [leafEntryBill,Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul] using hm
  apply h.trans
  unfold rawLeafCap
  exact (Nat.add_le_add_right (Nat.add_le_add_right checked _) _).trans_eq (by ring)

#print axioms raw_code_gate_fee
#print axioms literal_read_cmd_upper
#print axioms same_row_interpreter_fee

end J6R62Leaf
