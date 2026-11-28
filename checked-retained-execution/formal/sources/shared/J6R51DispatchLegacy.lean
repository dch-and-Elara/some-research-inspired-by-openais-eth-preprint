import J6R51DispatchLookupIndex
import J6R51DispatchOrdinal
import J6R49DFSProbe
import J6R26DescriptorTreeNative

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 2700

/-! The opaque legacy list order is actually read, rather than
stipulated equal to the live weighted cursor. The file is an input
with checked bytes and explicit size; its production is not proven. -/
namespace J6R51Dispatch
open scoped Polynomial Classical
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion J6R49DFS

set_option linter.unusedSimpArgs false in
theorem idx_of_real_beq_encoding {X Y : Type*}
    [BEq X] [LawfulBEq X] [BEq Y] [LawfulBEq Y]
    (enc : X → Y) (hinj : Function.Injective enc) (mode : X) (order : List X) :
    (order.map enc).idxOf (enc mode)=order.idxOf mode := by
  induction order with
  | nil => rfl
  | cons x xs ih =>
    by_cases e : x=mode
    · subst x
      simp
    · have ne : enc x≠enc mode := fun h=>e (hinj h)
      have h1 : (x == mode)=false := Bool.eq_false_iff.mpr (fun h=>e (beq_iff_eq.mp h))
      have h2 : (enc x == enc mode)=false := Bool.eq_false_iff.mpr (fun h=>ne (beq_iff_eq.mp h))
      simp [List.idxOf_cons,h1,h2,ih]

theorem same_index_for_lawful_comparators {X : Type*} (b₁ b₂ : BEq X)
    (h₁ : @LawfulBEq X b₁) (h₂ : @LawfulBEq X b₂) (x : X) (order : List X) :
    @List.idxOf X b₁ x order = @List.idxOf X b₂ x order := by
  rcases b₁ with ⟨u⟩
  rcases b₂ with ⟨v⟩
  have eq : u=v := by
    funext a b
    apply Bool.eq_iff_iff.mpr
    exact (@beq_iff_eq X ⟨u⟩ h₁ a b).trans (@beq_iff_eq X ⟨v⟩ h₂ a b).symm
  cases eq
  rfl

def lookupAndIssue {q tc tz tm : ℕ} (query : List (Word q))
    (file : List (List (Word q))) (t : Word tc) (z : Word tz) (g : Word 6) :
    Meter (Option (Word (tc+(tz+(tm+6))))) :=
  let m := readPriorOrdinal (tm:=tm) query file
  match m.result with
  | none => ⟨none,m.steps+4⟩
  | some clock =>
    let out := preparedKey t z clock g
    ⟨some out.result,m.steps+out.steps+4⟩

variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

noncomputable def frozenCatalogueBytes (T : Prepared cfg sel r hf) (v : Ticket sel r)
    (I : SiteTape sel (ticketReady T v) v.centerAt q) : List (List (Word q)) :=
  ((ticketActive T v).tape v.centerAt).modes.map
    (fun β=>(vectorKey sel (ticketReady T v) v.centerAt I β).map word)

theorem live_event_encoding_injective (T : Prepared cfg sel r hf) (v : Ticket sel r)
    (I : SiteTape sel (ticketReady T v) v.centerAt q) :
    Function.Injective (fun β=>(vectorKey sel (ticketReady T v) v.centerAt I β).map (word (q:=q))) := by
  intro β γ raw
  have Lift (μ : NativeMenu (N sel) v.parent v.centerAt) :
      ((vectorKey sel (ticketReady T v) v.centerAt I μ).map (word (q:=q))).map Word.val =
        vectorKey sel (ticketReady T v) v.centerAt I μ := by
    rw [List.map_map]
    exact (List.map_congr_left
        (fun w (mem : w∈vectorKey sel (ticketReady T v) v.centerAt I μ) =>
          word_val (actual_legal_coordinates_fit I μ w mem))).trans (List.map_id _)
  have h := congrArg (List.map Word.val) raw
  rw [Lift β,Lift γ] at h
  exact vector_key_inj sel (ticketReady T v) v.centerAt I h

theorem read_actual_frozen_order_and_issue (T : Prepared cfg sel r hf) (v : Ticket sel r)
    (I : SiteTape sel (ticketReady T v) v.centerAt q)
    {port edge dep prec tc tz tm : ℕ}
    (D : NativeJob T v port edge dep prec tc tz tm)
    (file : List (List (Word q))) (fileExact : file=frozenCatalogueBytes T v I)
    (query : List (Word q)) (actual : query.map Word.val=vectorKey sel (ticketReady T v) v.centerAt I v.modeAt)
    (ht : 0<tm) (fit : file.length<2^tm) :
    let out := lookupAndIssue (tm:=tm) query file D.tWord D.zWord D.gWord
    (out.result.map Word.bits)=some D.coordinates ∧
    out.steps ≤ 3*tm+7+file.length*(query.length*(10*q+9)+13*tm+12)+
      (6*(tc+(tz+(tm+6)))+10)+4 := by
  let μ := v.modeAt
  let modes := ((ticketActive T v).tape v.centerAt).modes
  let enc := fun β=> (vectorKey sel (ticketReady T v) v.centerAt I β).map (word (q:=q))
  have dense : enc μ=query := by
    change (vectorKey sel (ticketReady T v) v.centerAt I v.modeAt).map (word (q:=q))=query
    rw [←actual,List.map_map]
    exact (List.map_congr_left (fun u (_ : u∈query)=>valued_word u)).trans (List.map_id _)
  have fileSpec : file=modes.map enc := fileExact
  have contains : query∈file := by
    rw [←dense,fileSpec]
    exact List.mem_map_of_mem (f:=enc) (((ticketActive T v).tape v.centerAt).modeComplete μ)
  have idx : file.idxOf query=modeOrdinal T v := by
    rw [←dense,fileSpec]
    refine (idx_of_real_beq_encoding enc (live_event_encoding_injective T v I) μ modes).trans ?_
    unfold modeOrdinal
    apply same_index_for_lawful_comparators <;> infer_instance
  obtain ⟨m,fee⟩ := read_prior_ordinal_correct (tm:=tm) query file ht fit contains
  have eq : (word (q:=tm) (file.idxOf query))=D.mWord := by
    rw [idx,←D.mExact,valued_word]
  rw [eq] at m
  obtain ⟨bits,cost⟩ := prepared_key_exact D.tWord D.zWord D.mWord D.gWord
  unfold lookupAndIssue
  dsimp only
  rw [m]
  dsimp only
  refine ⟨?_,?_⟩
  · rw [bits]
    rfl
  · rw [cost]
    exact Nat.add_le_add_right (Nat.add_le_add_right fee _) _

#print axioms idx_of_real_beq_encoding
#print axioms same_index_for_lawful_comparators
#print axioms frozenCatalogueBytes
#print axioms live_event_encoding_injective
#print axioms read_actual_frozen_order_and_issue
end J6R51Dispatch

