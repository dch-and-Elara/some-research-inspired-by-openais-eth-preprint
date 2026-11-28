import J6R53OldOwnerRootBasis
import J6R53OldOwnerRootParse
import J6R51IngressClaimRanks

/-! The actual fresh source's old rows read their own parsed ordinal
gate head; the physical padding and subdivision gates have exact
local opcodes. All suffix words are emitted by the paid root chart
reader. Only the complete ordered owner scope/key plan is supplied. -/
namespace J6R53OldOwnerRoot
open scoped Classical
open Std.Sat AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf
open J6R25PreparedSupply J6R31RootResidentTables J6R30GeneratedRootLayout
open J6R32RootGeneratedRegistryInputs J6R53TerminalGate J6R24LegalLayout J6OrientedHost J6Mesh
open J6R28GeneratedRootFrame J6R35RootOrigins J6R36ChildFramedRoute
open J6R53OldOwner J6R51Ingress J6R49RootIngress J7R9Compiler J7R9Subdivision J7R10Plant
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3600
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V] (H : CNF V) (s : DeclaredOrder V)
variable (rank : ℕ)
local notation "P" => (freshPlant H s)
local notation "N" => (SourceVertex (freshPlant H s))

theorem actual_old_head_by_rank (heads : List GateHead)
    (trueHeads : heads=(oldRoster H s).map (fun v=>gateHead (orderedGate H v)))
    (fits : (oldRoster H s).length≤2^rank) (x : OrderedOld H) :
    (selectHead heads (.old (wordAt rank ((rosterRank H s) x).val))).result=
      some (gateHead (orderedGate H x)) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (old_roster_all H s x)
  subst x
  unfold selectHead
  rw [(seek_record_exact _ _).1]
  change heads[bitsValue (AOracleMachineTimeTape.encodeBits rank ((rosterRank H s) ((oldRoster H s).get i)).val)]?=_
  rw [rank_at_roster_index, AOracleMachineTimeTape.encodeBits_exact _ _ (i.isLt.trans_le fits),trueHeads]
  simp [i.isLt]

def freshHeadChoice (v : N) : HeadChoice rank :=
  match v with
  | .inl (.inl (u,_))=>.old (wordAt rank ((rosterRank H s) u).val)
  | .inl (.inr (_,true))=>.free
  | .inl (.inr (_,false))=>.forceZero
  | .inr _=>.equal

theorem matched_fresh_root_opcode (heads : List GateHead)
    (trueHeads : heads=(oldRoster H s).map (fun v=>gateHead (orderedGate H v)))
    (fits : (oldRoster H s).length≤2^rank) (x : N) :
    (selectHead heads (freshHeadChoice H s rank x)).result=
      some (gateHead (rootLocalGate P x).gate) := by
  rcases x with ((⟨u,j⟩|⟨p,b⟩)|x)
  · exact actual_old_head_by_rank H s rank heads trueHeads fits u
  · cases b <;> rfl
  · rfl

section WholeFresh
variable {V₀ : Type} [DecidableEq V₀] [Fintype V₀]
variable (F : CNF V₀) (vars : DeclaredOrder V₀) (code : V₀→List Bool)
variable {h d j r c e own key prec page : ℕ}
local notation "HF" => (guardedInOrder F vars.roster)
local notation "S" => (guardRoster vars)
local notation "PlantF" => (freshPlant (guardedInOrder F vars.roster) (guardRoster vars))
local notation "VerticesF" => (SourceVertex (freshPlant (guardedInOrder F vars.roster) (guardRoster vars)))
local notation "Mass" => (nWires (guardedInOrder F vars.roster))

def mountFreshRootOwnerRoster
    (C : Meter (LiteralPortFile PlantF r c e))
    (axis : List Bool) (clock : axis.length=(oddAxis Mass).val)
    (inj : Function.Injective code) (hh : 0<h) (hd : 0<d) (hj : 0<j)
    (fitH : (HF).length≤2^h) (fitD : ∀ row∈HF,row.length≤2^d)
    (fitJ : ∀ v,(occurrences HF v).length-3≤2^j)
    (rank : ℕ) (rankFit : (oldRoster HF S).length≤2^rank)
    (name : VerticesF→Word own) (origin : VerticesF→Origin key prec page)
    (order : List VerticesF) (unique : order.Nodup) (all : ∀ u,u∈order)
    (plans : Meter (List (OwnerPlan own rank (SuffixKeyWidth Mass) key prec page)))
    (aligned : plans.result=order.map (rootPlanWord PlantF name origin (freshHeadChoice HF S rank))) :
    Meter (CompleteRoster name (actualOwnerValue (rootLocalGate PlantF) (rootOperand PlantF) origin)) :=
  let heads := rawRootHeads (h:=h) (d:=d) (j:=j) (vars.roster.map code) (codeCNF code F)
  have head := raw_fresh_root_heads_actual (h:=h) (d:=d) (j:=j)
    F vars code inj hh hd hj fitH fitD fitJ
  let out := mountSourceFromParsedHeads PlantF C.result axis clock name origin (freshHeadChoice HF S rank)
    heads (matched_fresh_root_opcode HF S rank heads.result head rankFit) order unique all plans aligned
  ⟨out.result,C.steps+out.steps⟩

theorem fresh_original_owner_in_real_roster
    (C : Meter (LiteralPortFile PlantF r c e))
    (axis : List Bool) (clock : axis.length=(oddAxis Mass).val)
    (inj : Function.Injective code) (hh : 0<h) (hd : 0<d) (hj : 0<j)
    (fitH : (HF).length≤2^h) (fitD : ∀ row∈HF,row.length≤2^d)
    (fitJ : ∀ v,(occurrences HF v).length-3≤2^j)
    (rank : ℕ) (rankFit : (oldRoster HF S).length≤2^rank)
    (name : VerticesF→Word own) (origin : VerticesF→Origin key prec page)
    (order : List VerticesF) (unique : order.Nodup) (all : ∀ u,u∈order)
    (plans : Meter (List (OwnerPlan own rank (SuffixKeyWidth Mass) key prec page)))
    (aligned : plans.result=order.map (rootPlanWord PlantF name origin (freshHeadChoice HF S rank)))
    (uniqueNames : Function.Injective name) (x : VerticesF) :
    let out := mountFreshRootOwnerRoster F vars code C axis clock inj hh hd hj fitH fitD fitJ
      rank rankFit name origin order unique all plans aligned
    (locate (name x) out.result.raw).result=
      some (actualOwnerValue (rootLocalGate PlantF) (rootOperand PlantF) origin x) :=
  complete_owner_hit _ uniqueNames x
end WholeFresh

#print axioms actual_old_head_by_rank
#print axioms matched_fresh_root_opcode
#print axioms mountFreshRootOwnerRoster
#print axioms fresh_original_owner_in_real_roster
end
end J6R53OldOwnerRoot
