
import A2R45LiteralAllModesSource
import A2R45LiteralAllModesPlainHost
import J6R12RepackReadNatural
import J6R11Threshold
import J6R12Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7500000
set_option synthInstance.maxHeartbeats 170000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

/-! Original A2 all-mode oracle on the already normalized ordinary
literal sparse CNF, with no guard clause, planted copy, or repaired
padding. Keep availability of the exact completed oracle explicit.
The statement here concerns the actual prepared active root; it does
not meter initial normalization, field search, or oracle evaluation. -/
namespace A2R45Literal
open scoped Classical Polynomial BigOperators
open Polynomial Std.Sat J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R11Blueprint J6R12Blueprint J6R12Repack J6R11Threshold
open J7R9Compiler J7R10Plant J1PPrinted J6R10Repack J6R11Repack

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V)

def sparseS : ℕ := Fintype.card V+F.length

def sparseRoot (f : ℤ[X]) : Call (PhysicalHost f 1) :=
  let H := plainHost (physicalPlant F) f (Fintype.card V+1)
  ⟨H,0,nWires F,Fintype.card V+1⟩

theorem literal_sparse_source_count (f : ℤ[X]) (hf : f.Monic) (hF : 0<f.natDegree)
    (occurs : AllOccur F) :
    (sparseRoot F f).host.contract hf=(PinnedCNF.modelCount F:IntRing f 1) := by
  change (plainHost (physicalPlant F) f (Fintype.card V+1)).contract hf=_
  rw [plain_contract_card _ f _ (Nat.succ_pos _) hf hF,plant_count F occurs]

theorem literal_sparse_source_size (f : ℤ[X]) (occurs : AllOccur F)
    (nonempty : ∀ c∈F,0<c.length) (width : ∀ c∈F,c.length≤3) :
    sparseS F≤(sparseRoot F f).edges ∧ (sparseRoot F f).edges≤12*sparseS F := by
  obtain ⟨hlo,hhi⟩ := J7R9Size.source_size F 3 occurs nonempty width
  constructor
  · exact hlo
  · exact hhi.trans (Nat.mul_le_mul_left 12 (Nat.le_add_left F.length (Fintype.card V)))

theorem literal_sparse_degree (f : ℤ[X]) (width : ∀ c∈F,c.length≤3) :
    GoodDegree (sparseRoot F f).host 3 := by
  constructor
  · intro v
    change Nat.card {e : Fin (nWires F)//(plainNetwork (physicalPlant F)).row e=v}≤3
    rw [plain_actual_row_size]
    exact J7R10Ports.degree_bound F 3 width v
  · intro v
    change Nat.card {e : Fin (nWires F)//(plainNetwork (physicalPlant F)).col e=v}≤3
    rw [plain_actual_column_size]
    decide

theorem raw_models_fit (f : ℤ[X]) :
    PinnedCNF.modelCount F<2^(sparseRoot F f).prec := by
  have hb : PinnedCNF.modelCount F≤2^(Fintype.card V) := by
    rw [modelCount_card F,Nat.card_eq_fintype_card]
    have h := Fintype.card_le_of_injective _
      (Subtype.val_injective : Function.Injective
        (Subtype.val : {x : V→Bool//CNF.Sat x F}→(V→Bool)))
    simpa only [Fintype.card_fun,Fintype.card_bool] using h
  exact hb.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

variable (f : ℤ[X])
local notation "s" => sparseS F
local notation "c" => sparseRoot F f
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s

theorem sparse_all_modes_recovers_count
    (occurs : AllOccur F) (nonempty : ∀ cl∈F,0<cl.length) (width : ∀ cl∈F,cl.length≤3)
    (cfg : RootBounds s 12 f) (sel : Selector S Δ)
    (d : @J6R12Blueprint.Ready f 1 S Δ c) (hf : f.Monic)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (oracle : WholeAnswers S f 1 c)
    (correct : ∀ t z,oracle t z=actualWhole sel d hf t z) :
    boxNatural f 1 (c).prec hf (wholeAssemble S f 1 c d.fit oracle)=PinnedCNF.modelCount F := by
  have size : 8^(c).depth*(c).edges≤12*s := by
    change 1*(c).edges≤12*s
    rw [one_mul]
    exact (literal_sparse_source_size F f occurs nonempty width).2
  have hw := printed_taper_legal s (c).edges 12 (c).depth
    cfg.widthPos cfg.constPos cfg.size d.active size
  have hd := J6R12Bounds.positive_degree cfg
  have e := exact_aggregate_client sel d hf hd hw.1 hw.2.2 oracle correct
  rw [e,literal_sparse_source_count F f hf hd occurs,map_natCast]
  exact boxNatural_of_nat f 1 (c).prec hf (Nat.succ_pos _) (by decide) hd _ (raw_models_fit F f)

#print axioms literal_sparse_source_count
#print axioms literal_sparse_source_size
#print axioms literal_sparse_degree
#print axioms raw_models_fit
#print axioms sparse_all_modes_recovers_count
end
end A2R45Literal
