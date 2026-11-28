import J6R62LeafReader
import J6R53TerminalGateCached

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 21000000
set_option maxRecDepth 3100

/-! Finite charges of the terminal's scans of the installed parent frames.
The only budgets are ordinary byte lengths, never a fee callback. -/
namespace J6R62Leaf
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R34ChildPath J6R36ChildFramedRoute J6R51ParentFrames J6R52Terminal
open J6R53TerminalGate J6R50Leaf J6R27OriginalGate J6R49SourceLayout J6R51Leaf J6R19Retained

def FramesFit {w own key prec page : ℕ} (fs : List (FramedEdge w own key prec page)) (U : ℕ) : Prop :=
  ∀ t∈fs,t.left.body.length≤U ∧ t.right.body.length≤U

def RequestsFit {w : ℕ} (rs : List (WireRequest w)) (U : ℕ) : Prop :=
  ∀ t∈rs,t.ancestry.length≤U

theorem origin_fee_upper (key prec page : ℕ) (hit : Bool) :
    originFee key prec page hit ≤ originFee key prec page true := by
  cases hit <;> simp [originFee]

def jacketCap (w own key prec page U : ℕ) :=
  (3*own+1)+2*originFee key prec page true+2*(3*w+1)+2*(3*U+1)+12

theorem frame_fee_under_real_word_width {w own key prec page U : ℕ}
    (x : FramedEdge w own key prec page) (l : x.left.body.length≤U) (r : x.right.body.length≤U) :
    framedIncidenceFee x≤jacketCap w own key prec page U := by
  have a := origin_fee_upper key prec page x.left.origin.pageKey.isSome
  have b := origin_fee_upper key prec page x.right.origin.pageKey.isSome
  unfold framedIncidenceFee jacketCap
  omega

theorem retained_scan_bounded {w own key prec page U : ℕ}
    (fs : List (FramedEdge w own key prec page)) (h : FramesFit fs U) (id : Word own) :
    let r := collectRetained id fs
    r.result.length≤fs.length ∧ RequestsFit r.result U ∧
      r.steps≤3+fs.length*(10*own+11+wireFee w U) := by
  dsimp only
  rw [(collect_retained_exact id fs).1,(collect_retained_exact id fs).2]
  constructor
  · rw [List.length_map]
    exact List.length_filter_le _ _
  · constructor
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      exact (h x (List.mem_of_mem_filter hx)).1
    · apply Nat.add_le_add_left
      apply sum_map_cap
      intro x hx
      have hh := (h x hx).1
      unfold retainVisitFee wireFee
      split <;> omega

theorem fresh_scan_bounded {w own key prec page U : ℕ}
    (fs : List (FramedEdge w own key prec page)) (h : FramesFit fs U) (pg : Word page) :
    let r := scanFresh pg fs
    r.result.length≤fs.length ∧ RequestsFit r.result U ∧
      r.steps≤3+fs.length*(10*page+11+wireFee w U) := by
  dsimp only
  rw [scan_fresh_exact]
  constructor
  · exact List.length_filterMap_le _ _
  · constructor
    · intro y hy
      obtain ⟨x,hx,hh⟩ := List.mem_filterMap.mp hy
      have descent : y=requestView x.right := by
        unfold chooseFresh at hh
        cases he : x.right.origin.pageKey with
        | none => simp [he] at hh
        | some nm =>
          simp only [he] at hh
          split at hh
          · exact (Option.some.inj hh).symm
          · contradiction
      rw [descent]
      exact (h x hx).2
    · apply Nat.add_le_add_left
      apply sum_map_cap
      intro x hx
      have hh := (h x hx).2
      unfold freshVisitFee wireFee
      cases x.right.origin.pageKey with
      | none =>
        dsimp only
        omega
      | some nm =>
        dsimp only
        split <;> omega

theorem seek_lane_bounded {w : ℕ} (q : Word w) (keys : List (Word w)) :
    (seekLane q keys).steps≤2+keys.length*seekStride w ∧
      ∀ us, (seekLane q keys).result=some us → us.length≤keys.length := by
  induction keys with
  | nil => simp [seekLane]
  | cons k ks ih =>
    have hm := (cmpAddr_exact q k).2
    dsimp only [seekLane]
    split <;> dsimp only
    · constructor
      · rw [hm,List.length_cons,Nat.add_mul,one_mul,seekStride]
        omega
      · rintro us e
        obtain rfl := Option.some.inj e
        simp
    · constructor
      · rw [hm,List.length_cons,Nat.add_mul,one_mul]
        have hz := ih.1
        unfold seekStride at *
        omega
      · intro us h
        cases gr : (seekLane q ks).result with
        | none => simp [gr] at h
        | some old =>
          have hh := ih.2 old gr
          obtain rfl := Option.some.inj (by simpa only [gr,Option.map_some] using h)
          simpa only [List.length_cons] using Nat.succ_le_succ hh

theorem wire_emission_fee {w U : ℕ} (keys : List (Word w)) (reqs : List (WireRequest w))
    (h : RequestsFit reqs U) :
    (emitWires keys reqs).steps ≤ 4+reqs.length*(keys.length*seekStride w+3*U+12) := by
  induction reqs with
  | nil => simp [emitWires]
  | cons q qs ih =>
    have hs := (seek_lane_bounded q.incumbent keys).1
    have hq := h q List.mem_cons_self
    have ht := ih (fun x hx=>h x (List.mem_cons_of_mem _ hx))
    have here : (emitWire keys q).steps ≤ keys.length*seekStride w+3*U+8 := by
      simp only [emitWire,copyBytes_exact]
      omega
    simp only [emitWires]
    cases hz : (emitWire keys q).result <;> dsimp only
    all_goals
      rw [List.length_cons, Nat.add_mul, one_mul]
      omega

theorem depth_prefix_fee (s : List Bool) :
    (readDepthPrefix s).steps≤4*s.length+3 := by
  induction s with
  | nil => simp [readDepthPrefix]
  | cons a s ih =>
    cases a
    · simp [readDepthPrefix]; omega
    · simp [readDepthPrefix]

theorem request_depth_fee {w U : ℕ} (rs : List (WireRequest w)) (h : RequestsFit rs U) :
    (requestDepth rs).steps≤4*U+6 := by
  cases rs with
  | nil => simp [requestDepth]
  | cons a as =>
    have hm := depth_prefix_fee a.ancestry
    have hh := h a List.mem_cons_self
    change (readDepthPrefix a.ancestry).steps+3≤_
    omega

theorem suffix_fee_from_actual_length (a : ℕ) (hs : List Bool) :
    (suffix a hs).steps≤9+8*a+5*hs.length := by
  change (ahead a hs).steps+(lag hs (ahead a hs).result).steps+
    (scanWidth a (lag hs (ahead a hs).result).result).steps+4≤_
  rw [ahead_exact]
  dsimp only
  rw [lag_exact]
  dsimp only
  rw [(scanWidth_exact _ _).2]
  have h₁ := min_le_left a hs.length
  have h₂ := min_le_left hs.length (hs.drop a).length
  omega

theorem suffix_table_fee {W : ℕ} (a U : ℕ) (rs : List (WireRequest W))
    (h : RequestsFit rs U) :
    (suffixTable a rs).result.length=rs.length ∧
      (suffixTable a rs).steps≤3+rs.length*(17+8*a+3*W+5*U) := by
  induction rs with
  | nil => simp [suffixTable]
  | cons x xs ih =>
    obtain ⟨el,hm⟩ := ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    have hh := suffix_fee_from_actual_length a x.ancestry
    have hw := h x List.mem_cons_self
    simp only [suffixTable,List.length_cons,el,copy_fixed_exact,Nat.add_mul,one_mul]
    exact ⟨trivial,by omega⟩

#print axioms frame_fee_under_real_word_width
#print axioms retained_scan_bounded
#print axioms fresh_scan_bounded
#print axioms wire_emission_fee
#print axioms request_depth_fee
#print axioms suffix_table_fee

end J6R62Leaf
