import J6R48LeafRawReader
import J6R21LeafEnvelope
import J6R21LeafClock

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9700000
set_option maxRecDepth 2350

/-! Explicit ordered leaf code tape and unary recursion clock. Each
Boolean edge assignment visits the same entire code tape, including
both paid registry searches for a live generated entry. No indexed
vertex-to-routine lookup is an operation of this interpreter. -/
namespace J6R48Leaf
open scoped Classical BigOperators Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6ActiveRun J6R10Repack J6R11Blueprint J6R21Leaf J6R22Active
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
variable {c : Call (PhysicalHost f ell)}
local notation "Bnk" => PageBank f ell key prec tw bw page

structure RawTape (c : Call (PhysicalHost f ell)) (key page : ℕ) where
  clock : List Unit
  clockExact : clock.length=c.edges
  rows : List ((c.host.Row⊕c.host.Col)×PageReadCode c.edges key page)

def PagedLeaf.toRaw (D : PagedLeaf c key page) : RawTape c key page :=
  ⟨D.clock,D.clockShape,D.nodes.map (fun t=>(t,D.route t))⟩

def runTape (D : RawTape c key page) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : Bnk) : Meter (Block F ell) :=
  clockDFS F.hp (readProduct F.hp F.sizePos hEll D.rows (fun r=>r.2.run hf F hEll B)) D.clock []

def prepriced (D : RawTape c key page) (F : Frame f c.prec) (B : Bnk) : ℕ :=
  (D.rows.map (fun r=>rawPageFee F.words.length c.prec c.edges B r.2)).sum

def HasResidentFormat (D : RawTape c key page) (B : Bnk) : Prop :=
  ∀ r∈D.rows, ResidentReadForm B r.2

theorem raw_leaf_is_same_dispatch (D : PagedLeaf c key page) (hf : f.Monic)
    (F : Frame f c.prec) (hEll : 0<ell) (B : Bnk) :
    runTape (PagedLeaf.toRaw D) hf F hEll B=D.execute hf F hEll B := by
  unfold runTape PagedLeaf.toRaw PagedLeaf.execute
  congr 1
  funext xs
  exact readProduct_mapped F.hp F.sizePos hEll _ _ D.nodes xs

private theorem map_bill_le {α : Type*} (xs : List α) (u v : α→ℕ)
    (h : ∀ a∈xs,u a≤v a) : (xs.map u).sum≤(xs.map v).sum := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih (fun b hb=>h b (List.mem_cons_of_mem _ hb)))

theorem raw_leaf_actual_visits (D : RawTape c key page) :
    (∑ _ : Fin c.edges→Bool,D.rows.length)=2^c.edges*D.rows.length :=
  leaf_callback_visit_count c.edges D.rows

theorem prepriced_leaf_bill (D : RawTape c key page) (hf : f.Monic)
    (F : Frame f c.prec) (hEll : 0<ell) (B : Bnk) (form : HasResidentFormat D B) :
    leafEntryBill c.edges D.rows (fun r=>r.2.run hf F hEll B)≤2^c.edges*prepriced D F B := by
  have h (x : Fin c.edges→Bool) :
      thisVertexBill D.rows (fun r=>r.2.run hf F hEll B) (List.ofFn x)≤prepriced D F B :=
    map_bill_le D.rows _ _ (fun r hr=>raw_paged_read_bound hf F hEll B r.2 (form r hr)
      (List.ofFn x) List.length_ofFn)
  have total := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin c.edges→Bool))) (fun x _=>h x)
  have card : Fintype.card (Fin c.edges→Bool)=2^c.edges := by simp
  simpa only [leafEntryBill,Finset.sum_const,Finset.card_univ,card,nsmul_eq_mul] using total

def rawLeafCap (e ell p M v bill : ℕ) (hp : 0<p) :=
  2^M*(bill+uvWidth e ell p+v*(mulCap e ell p+2)+reverseFee M)+(2^M-1)*innerFee e ell p hp

theorem raw_leaf_steps (D : RawTape c key page) (hf : f.Monic)
    (F : Frame f c.prec) (hEll : 0<ell) (B : Bnk) (form : HasResidentFormat D B) :
    (runTape D hf F hEll B).steps≤
      rawLeafCap F.words.length ell c.prec c.edges D.rows.length (prepriced D F B) F.hp := by
  rw [runTape,clocked_leaf_is_native_enumerator F.hp F.sizePos hEll D.rows _ D.clock D.clockExact]
  have cost := (leafCompute_bills_every_entry F.hp F.sizePos hEll c.edges D.rows
    (fun r=>r.2.run hf F hEll B)).2
  have h := prepriced_leaf_bill D hf F hEll B form
  refine cost.trans ?_
  unfold rawLeafCap
  simp only [Nat.mul_add]
  simp only [Nat.mul_add] at cost
  omega

theorem raw_leaf_cap_mono (e ell p bill : ℕ) (hp : 0<p) {M H v V : ℕ}
    (edges : M≤H) (vertices : v≤V) :
    rawLeafCap e ell p M v bill hp≤rawLeafCap e ell p H V bill hp := by
  have pw : (2:ℕ)^M≤2^H := Nat.pow_le_pow_right (by decide) edges
  unfold rawLeafCap reverseFee
  gcongr

#print axioms raw_leaf_is_same_dispatch
#print axioms raw_leaf_actual_visits
#print axioms prepriced_leaf_bill
#print axioms raw_leaf_steps
#print axioms raw_leaf_cap_mono
end J6R48Leaf
