
import J6R21LeafPlant
import J6R12RepackBoolean

/-! A surviving original gate can be queried at descendant precision
using the real original scoped ports, without assuming the other root
edges survived or reconstructing an entire old assignment. Routing the
typed scope to those descendant edge addresses is the external
retention obligation of the caller. -/
namespace J6R21Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint J6R11Repack J6OrientedHost
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7500000

structure LocalGate (P : Type) where
  degree : ℕ
  port : Fin degree→P
  gate : Gate degree

variable {S V : Type} [LinearOrder S] {a b m q l : ℕ}

abbrev PlantNode (_T : Plant V m q) (w : Fin a→S) :=
  Left V w m b l⊕Right w m b l q

abbrev PlantPorts (T : Plant V m q) (w : Fin a→S) (v : PlantNode (b:=b) (l:=l) T w) :=
  ParentPorts (rootNetwork (b:=b) (l:=l) T w) v

def plantRowLocal (T : Plant V m q) (w : Fin a→S)
    (v : Left V w m b l) (j : oldScope T w v) : PlantPorts T w (.inl v) :=
  ⟨.inl (rowPort T w v j),congrArg Sum.inl (root_row_owner T w v j)⟩

def plantColLocal (T : Plant V m q) (w : Fin a→S)
    (v : Right w m b l q) (j : Bool) : PlantPorts T w (.inr v) :=
  ⟨.inr (colPort T w v j),congrArg Sum.inr (root_col_owner T w v j)⟩

def originalPortGate (T : Plant V m q) (w : Fin a→S) :
    (v : PlantNode (b:=b) (l:=l) T w)→LocalGate (PlantPorts T w v)
  | .inl (.inl (u,j)) => ⟨T.degree u,plantRowLocal T w (.inl (u,j)),T.old u⟩
  | .inl (.inr (pad,tag)) =>
    ⟨1,fun _=>plantRowLocal T w (.inr (pad,tag)) (),
     if tag then Gate.free else Gate.clause (fun _=>false)⟩
  | .inr v => ⟨2,fun i=>plantColLocal T w v (i.val==1),Gate.equal⟩

def plantPortFlag (T : Plant V m q) (w : Fin a→S) :
    (v : PlantNode (b:=b) (l:=l) T w) → (PlantPorts T w v→Bool) → Bool
  | .inl v,y => rowTable T w v (fun i=>y (plantRowLocal T w v i))
  | .inr v,y => colTable w v (fun i=>y (plantColLocal T w v i))

theorem original_port_gate_flag (T : Plant V m q) (w : Fin a→S)
    (v : PlantNode (b:=b) (l:=l) T w) (y : PlantPorts T w v→Bool) :
    let G := originalPortGate T w v
    G.gate.eval (y∘G.port)=plantPortFlag T w v y := by
  rcases v with ((⟨u,j⟩|⟨pad,tag⟩)|v)
  · rfl
  · cases tag with
    | true => rfl
    | false =>
      change decide (∃ i : Fin 1,y (plantRowLocal T w (.inr (pad,false)) ())=false) =
        !(y (plantRowLocal T w (.inr (pad,false)) ()))
      cases y (plantRowLocal T w (.inr (pad,false)) ()) <;> simp
  · exact two_ports_truth (fun bit=>y (plantColLocal T w v bit))

theorem root_entry_flag_at_current {f : ℤ[X]} (ell created current : ℕ)
    (T : Plant V m q) (w : Fin a→S) (hf : f.Monic)
    (hp : 0<created) (hF : 0<f.natDegree) (hell : 0<ell)
    (v : PlantNode (b:=b) (l:=l) T w) (y : PlantPorts T w v→Bool) :
    (rootEntryFile f ell created T w v).read hf current y =
      if plantPortFlag T w v y then 1 else 0 := by
  have table : (rootEntryFile f ell created T w v).frozen hf y =
      canonicalLift created f hf ell (if plantPortFlag T w v y then 1 else 0) := by
    cases v <;> rfl
  rw [CreatedEntry.read,table]
  cases h : plantPortFlag T w v y
  · simp only [Bool.false_eq_true,if_false,J6R12Repack.canonical_lift_zero,map_zero]
  · simp only [if_true,J6R12Repack.canonical_lift_one created hp f hf hF ell hell,map_one]

theorem actual_original_at_descendant_ports {f : ℤ[X]} {ell created current n k : ℕ}
    (T : Plant V m q) (w : Fin a→S) (hf : f.Monic)
    (hp : 0<created) (hq : 0<current) (hF : 0<f.natDegree) (hell : 0<ell)
    {fw : List (A1R10.Word current)} (he : 0<fw.length)
    (hPoly : Modulus current hq fw=NativeProbeRing.liftPoly current f)
    (v : PlantNode (b:=b) (l:=l) T w)
    (slot : PlantPorts T w v→Fin n) (fit : n≤2^k) (x : Fin n→Bool) :
    let G := originalPortGate T w v
    let A := gateTape fit (slot∘G.port) G.gate
    let out := uvGate hq he hell A (List.ofFn x)
    J6R18ChildWrite.castBox hPoly (uvRead hq fw ell out.result)=
      (rootEntryFile f ell created T w v).read hf current (x∘slot) ∧
      out.steps≤originalGateFee n k G.degree+uvWidth fw.length ell current+4 := by
  dsimp only
  let G := originalPortGate T w v
  obtain ⟨h,c⟩ := uv_gate_exact hq he hell fit (slot∘G.port) G.gate x
  refine ⟨?_,c⟩
  rw [h,root_entry_flag_at_current ell created current T w hf hp hF hell v (x∘slot),
    ← literalChart_is_cast]
  rw [show G.gate.eval (x∘(slot∘G.port))=plantPortFlag T w v (x∘slot)
    from original_port_gate_flag T w v (x∘slot)]
  split <;> simp only [map_one,map_zero]

#print axioms original_port_gate_flag
#print axioms root_entry_flag_at_current
#print axioms actual_original_at_descendant_ports
end J6R21Leaf
