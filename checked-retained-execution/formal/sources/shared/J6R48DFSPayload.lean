import J6R48DFSAtlas
import J6R21LeafWidth

/-! Explicit literal value fields of one active generated page. This
measures a fixed-width choice for these fields, separate
from record framing/length words, layout data or compiler scratch.
Ranks of mode orders are written at width p, a conservative width;
the resident signed context remains a separate per-creator field. -/
namespace J6R48DFS
open scoped Polynomial
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R18ChildWrite J6R21Ancestor J6R21Leaf J6R15ModeCost
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4200000

private theorem flatMap_length_le {A B : Type*} (xs : List A) (fn : A→List B) (b : ℕ)
    (h : ∀ x∈xs,(fn x).length≤b) :
    (xs.flatMap fn).length ≤ xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul,Nat.add_comm]
    exact Nat.add_le_add (ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))) (h x List.mem_cons_self)

private theorem flatMap_length_const {A B : Type*} (xs : List A) (fn : A→List B) (b : ℕ)
    (h : ∀ x∈xs,(fn x).length=b) :
    (xs.flatMap fn).length = xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul,
      h x List.mem_cons_self,ih (fun y hy=>h y (List.mem_cons_of_mem _ hy)),Nat.add_comm]

def modePayload {a p w : ℕ} {i : Fin a} (m : ModeInput a p i w) : List Bool :=
  m.code++m.tile.bits++AOracleMachineTimeTape.encodeBits p m.order.val++
    [m.targeted,m.sourced]++m.beta.bits

theorem mode_payload_length {a p w : ℕ} {i : Fin a} (m : ModeInput a p i w) :
    (modePayload m).length=m.code.length+(i.val+1)+p+2+w := by
  simp only [modePayload,List.length_append,m.tile.size,AOracleMachineTimeTape.encodeBits_length,
    List.length_cons,List.length_nil,m.beta.size]

def originPayload {a p ell w : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (o : OriginFields a p ell w fw i) : List Bool :=
  leafPayload o.probe++o.rows.flatMap Word.bits++o.cols.flatMap Word.bits++o.modes.flatMap modePayload

theorem origin_payload_length {a p ell w : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (o : OriginFields a p ell w fw i) :
    (originPayload o).length =
      ell*(fw.length*p)+o.rows.length*a+o.cols.length*a+(o.modes.flatMap modePayload).length := by
  rw [originPayload,List.length_append,List.length_append,List.length_append,leaf_payload_width,
    flatMap_length_const o.rows Word.bits a (fun x _=>x.size),
    flatMap_length_const o.cols Word.bits a (fun x _=>x.size)]

theorem explicit_page_payload_bound {a p ell w : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (o : OriginFields a p ell w fw i) (R C μ b : ℕ)
    (hR : o.rows.length≤R) (hC : o.cols.length≤C) (hM : o.modes.length≤μ)
    (hCode : ∀ m∈o.modes,m.code.length≤b) :
    (originPayload o).length ≤ ell*(fw.length*p)+R*a+C*a+μ*(b+(i.val+1)+p+2+w) := by
  rw [origin_payload_length]
  have hModes := flatMap_length_le o.modes modePayload (b+(i.val+1)+p+2+w) (fun x hx=>by
    rw [mode_payload_length]
    have h := hCode x hx
    omega)
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ hR) _) (Nat.mul_le_mul_right _ hC))
    (hModes.trans (Nat.mul_le_mul_right _ hM))

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page

def envelopePages (e : PagedEnvelope f ell prec page) : List (List Bool) :=
  e.pages.map (fun y=>y.address.bits++originPayload y.payload)

def residentAtlasBits (B : L) : ℕ :=
  (B.records.map (fun r=>((envelopePages r.payload.payload).map List.length).sum)).sum

theorem envelope_page_payload_bound (e : PagedEnvelope f ell prec page) (U : ℕ)
    (fit : ∀ y∈e.pages,(originPayload y.payload).length≤U) :
    ((envelopePages e).map List.length).sum≤e.pages.length*(page+U) := by
  unfold envelopePages
  rw [List.map_map]
  let S := e.shape
  let payload := fun (y : RefRow page (OriginFields S.a S.p ell S.w S.old S.i)) =>
    (y.address.bits++originPayload y.payload).length
  have bill (rows : List (RefRow page (OriginFields S.a S.p ell S.w S.old S.i)))
      (h : ∀ y∈rows,(originPayload y.payload).length≤U) :
      (rows.map payload).sum ≤ rows.length*(page+U) := by
    induction rows with
    | nil => simp
    | cons x xs ih =>
      rw [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm]
      have hx : payload x ≤ page+U := by
        unfold payload
        rw [List.length_append,x.address.size]
        exact Nat.add_le_add_left (h x List.mem_cons_self) _
      exact Nat.add_le_add (ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))) hx
  exact bill e.pages fit

/-- Counts the explicitly represented page key, probe, row/column,
mode-code, order, flag and exponent bit fields on live ancestors.
A per-page U must be proven separately for the supplied compiler.
An upper bound for these payload fields is not a peak bound for
allocating any entire recursion machine, or its root/scratch data. -/
theorem scoped_generated_literal_page_bits
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page) (initial : L) (U : ℕ)
    (hRows : AllExactPages born)
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
      let e := (born p w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤U)
    (p : Path sel r c) :
    residentAtlasBits (stackBank born initial p) ≤
      residentAtlasBits initial+((96*r.edges)/29)*(page+U) := by
  have induction_bound :
      residentAtlasBits (stackBank born initial p) ≤ residentAtlasBits initial+pagesOnStack p*(page+U) := by
    induction p with
    | root => simp only [stackBank,pagesOnStack,Nat.zero_mul,Nat.add_zero,le_refl]
    | step p w ih =>
      let e := (born p w).job.immutable.payload.payload
      change ((envelopePages e).map List.length).sum+
        residentAtlasBits (stackBank born initial p) ≤
          residentAtlasBits initial+(pagesOnStack p+newPages (sel:=sel) w)*(page+U)
      have h := envelope_page_payload_bound e U (fit p w)
      change ((envelopePages e).map List.length).sum≤ e.pages.length*(page+U) at h
      rw [show e.pages.length=newPages (sel:=sel) w from hRows p w] at h
      rw [Nat.add_mul]
      exact (Nat.add_le_add h ih).trans_eq (by ac_rfl)
  exact induction_bound.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (generated_packets_linear cfg T.rootStable p)) _)

#print axioms mode_payload_length
#print axioms origin_payload_length
#print axioms explicit_page_payload_bound
#print axioms envelope_page_payload_bound
#print axioms scoped_generated_literal_page_bits
end J6R48DFS
