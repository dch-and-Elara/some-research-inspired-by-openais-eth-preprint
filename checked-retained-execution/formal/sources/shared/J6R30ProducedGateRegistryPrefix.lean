
import J6R30ProducedGateRegistryInvoke

/-! Later DFS installations are not free cache hits. If no new key is
the ancestor's key, the actual reader reaches the identical immutable
capsule after scanning the new front. Exactly one reference-header
fee is billed for every such skipped row. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime A1R10 J6R21Ancestor J6R20Ancestor

theorem reference_front_fee {key : ℕ} {D : Type*}
    (addr : J6R15ModeCost.Word key) (front suffix : List (RefRow key D))
    (away : ∀ r∈front,r.address≠addr) :
    locate addr (front++suffix)=
      ⟨(locate addr suffix).result,front.length*refHeadFee key+(locate addr suffix).steps⟩ := by
  induction front with
  | nil => simp only [List.nil_append,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons r rs ih =>
    have h : (cmpAddr addr r.address).result≠true :=
      fun t=>away r List.mem_cons_self ((cmpAddr_exact _ _).1.mp t).symm
    rw [List.cons_append,locate,if_neg h]
    dsimp only
    rw [ih (fun r inR=>away r (List.mem_cons_of_mem _ inR)),(cmpAddr_exact _ _).2]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul,refHeadFee]
    congr 1
    omega

theorem invoke_bank_grown_cost {p q ell a w key prec tw bw : ℕ}
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (addr : J6R15ModeCost.Word key) (want : J6R15ModeCost.Word prec)
    (depth : ℕ) (raw : List Raw)
    (before after : GateLedger (ell:=ell) (w:=w) old i key prec tw bw)
    (front : List (RefRow key (Stored key prec tw bw (OriginFields a p ell w old i))))
    (grown : after.records=front++before.records)
    (away : ∀ r∈front,r.address≠addr) :
    let x := invokeFromBank hp he hEll hD addr want depth raw before
    invokeFromBank hp he hEll hD addr want depth raw after=
      ⟨x.result,x.steps+front.length*refHeadFee key⟩ := by
  have e := reference_front_fee addr front before.records away
  unfold invokeFromBank
  dsimp only
  rw [grown,e]
  cases h : (locate addr before.records).result <;> dsimp only
  all_goals congr 1; omega

theorem traced_read_grown_cost {p q ell a w key prec tw bw : ℕ}
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (addr : J6R15ModeCost.Word key) (want : J6R15ModeCost.Word prec)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool)
    (before after : GateLedger (ell:=ell) (w:=w) old i key prec tw bw)
    (front : List (RefRow key (Stored key prec tw bw (OriginFields a p ell w old i))))
    (grown : after.records=front++before.records)
    (away : ∀ r∈front,r.address≠addr) :
    let x := gatherAndInvoke hp he hEll hD addr want depth wires bits before
    gatherAndInvoke hp he hEll hD addr want depth wires bits after=
      ⟨x.result,x.steps+front.length*refHeadFee key⟩ := by
  have E := invoke_bank_grown_cost hp he hEll hD addr want depth
    (gather (depth+a+2) wires bits).result before after front grown away
  unfold gatherAndInvoke
  dsimp only
  rw [E]
  dsimp only
  congr 1
  omega

#print axioms reference_front_fee
#print axioms invoke_bank_grown_cost
#print axioms traced_read_grown_cost
end J6R30ProducedGateRegistry



