
import A2R45LiteralAllModesSparse

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 150000
set_option maxRecDepth 2150
set_option linter.unusedSectionVars false

/-! Discharge the active root guards for normalized (not guarded,
duplicated or repaired) literal 3CNF at the original s=n+m scale.
Field availability/size and the exact oracle answer are explicit. -/
namespace A2R45Literal
open scoped Classical Polynomial BigOperators
open Polynomial Std.Sat J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R11Blueprint J6R12Blueprint J6R12Repack
open J7R9Compiler J7R10Plant J1PPrinted J6R10Repack J6R11Repack

noncomputable section

theorem literal_cutoff_below_size (s L : ℕ) (hS : 2≤s) (hQ : 2≤L.sqrt) :
    J9PrintedSchedule.leafThreshold s L<s := by
  let q := L.sqrt
  have hq : 2≤q := hQ
  have hm : s≤q*(s-1) :=
    (by omega : s≤2*(s-1)).trans (Nat.mul_le_mul_right _ hq)
  have eq : s*q=q*(s-1)+q := by
    calc
      s*q=(s-1+1)*q := congrArg (·*q) (Nat.sub_add_cancel (show 1≤s by omega)).symm
      _=_ := by ring
  unfold J9PrintedSchedule.leafThreshold
  change (s+q-1)/q<s
  exact (Nat.div_lt_iff_lt_mul (by omega : 0<q)).mpr (by omega)

variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) (f : ℤ[X])
local notation "s" => sparseS F
local notation "c" => sparseRoot F f
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s

theorem normalized_sparse_ready (occurs : AllOccur F)
    (nonempty : ∀ cl∈F,0<cl.length) (w : ∀ cl∈F,cl.length≤3)
    (cfg : RootBounds s 12 f) :
    @J6R12Blueprint.Ready f 1 S Δ c := by
  have hs : 2≤s := (show (2:ℕ)≤12 from by decide).trans cfg.constSmall
  have hLambda : 4≤Nat.clog 2 s := by
    have h := (J9PrintedSchedule.rootU_range (Nat.clog 2 s)).1
    have h' := cfg.widthPos
    omega
  have hQ : 2≤(Nat.clog 2 s).sqrt := Nat.le_sqrt.mpr (by omega)
  have sz := literal_sparse_source_size F f occurs nonempty w
  have act : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)<(c).edges :=
    (literal_cutoff_below_size s _ hs hQ).trans_le sz.1
  have depth : 8^(c).depth*(c).edges≤12*s := by
    change 1*(c).edges≤12*s
    rw [one_mul]
    exact sz.2
  have hpack := (source_packing_conditions s (c).edges (c).depth cfg.widthPos act).2.2
  have hd : 3≤Δ :=
    ((show (3:ℕ)≤2*4 from by decide).trans
      (Nat.mul_le_mul_left 2 (stepL_ge_four (Nat.clog 2 s) (c).depth cfg.widthPos))).trans hpack
  have hdeg : GoodDegree (c).host Δ := by
    obtain ⟨a,b⟩ := literal_sparse_degree F f w
    exact ⟨fun r=>(a r).trans hd,fun col=>(b col).trans hd⟩
  have hcount : (c).host.edgeCount=(c).edges := by
    change Fintype.card (Fin (nWires F))=nWires F
    exact Fintype.card_fin _
  have tags : GoodTags (c).host (c).prec := by
    intro v
    exact le_rfl
  exact ready_of_size s 12 c cfg.constPos cfg.constSmall cfg.coefficient cfg.widthPos
    cfg.size act depth hcount hdeg tags

theorem source_sparse_all_modes_one_table
    (occurs : AllOccur F) (nonempty : ∀ cl∈F,0<cl.length) (w : ∀ cl∈F,cl.length≤3)
    (cfg : RootBounds s 12 f) (sel : Selector S Δ) (hf : f.Monic)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (oracle : WholeAnswers S f 1 c)
    (correct : ∀ t z,oracle t z=actualWhole sel (normalized_sparse_ready F f occurs nonempty w cfg) hf t z) :
    let d := normalized_sparse_ready F f occurs nonempty w cfg
    boxNatural f 1 (c).prec hf (wholeAssemble S f 1 c d.fit oracle)=PinnedCNF.modelCount F :=
  sparse_all_modes_recovers_count F f occurs nonempty w cfg sel
    (normalized_sparse_ready F f occurs nonempty w cfg) hf oracle correct

#print axioms literal_cutoff_below_size
#print axioms normalized_sparse_ready
#print axioms source_sparse_all_modes_one_table
end
end A2R45Literal
