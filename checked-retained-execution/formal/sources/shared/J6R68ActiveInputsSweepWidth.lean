import J6R68ActiveInputsSweepSetup

/-! Physical fields and per-centre tariffs of the real active sweep.
Widths refer to the raw stock payload and to the R49/R62 frame fields,
not to an unspecified heap or a supplied old active Meter. -/
namespace J6R68ActiveInputs.Sweep
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 J6R22Active J6ActiveSchedule
open J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49DFS J6R58ActivePrep J6R16ModeCost
open J6R62ActivePrep J6R63Active J6R64Active J6R67UnifiedRate J6R50Peak
open J6R17ModeTape J6R57ActiveFee J6R52FreshExterior J6R22RootReadout J6R32StatefulArithmetic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 25000000
set_option maxRecDepth 4100
set_option maxSynthPendingDepth 12
set_option Elab.async false

def stockAdmissionPx (K : ℕ) : ℕ :=
  (2*K+4*K+5)+taperFee K K+
    ((4*K+2)+(4*K+2)+16*(K+2)*K+heightWordRoof K+(4*K+4)+
      ((rosterRowBound K K K+5)*K+2)+8+commonLossWordRoof K K+4)+6

theorem stock_admission_from_actual_dimensions {a u q ew K : ℕ}
    (ha : a ≤ K) (hu : u ≤ K) (hq : q ≤ K) (he : ew ≤ K) (grid : 2^(a+1) ≤ K) :
    stockSetupRoof a u q ew ≤ stockAdmissionPx K := by
  unfold stockSetupRoof stockAdmissionPx taperFee baseTapeRoof commonLossWordRoof heightWordRoof
    rosterRowBound wordArithmeticRoof signedDivisionFee
  gcongr

def rawStockBits {q : ℕ} (B : RawBaseStock q) : ℕ :=
  B.margin.val.length+(B.rows.map (fun row=>row.key.length+row.multiplicity.val.length)).sum

def nthRowAddonPx (K : ℕ) : ℕ := (10*K+5)*K+6

def preparedCentrePx (K : ℕ) : ℕ := liveActiveTapeRoof K+nthRowAddonPx K

def mountedMaskPx (K : ℕ) : ℕ := K*(3*K+5)

noncomputable section
variable {f : ℤ[X]} {ell s C q pw ew cw n : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {good : n ≤ 2^f.natDegree}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth)
local notation "U" => (Shape.levelWidth (printedParams (f:=f) (ell:=ell) s) c.depth)

theorem exact_sweep_stock_width
    {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {bank : Bank f}
    (D : Schedule sel d bank q) :
    rawStockBits D.stock=q+(A+1+q)*D.stock.rows.length := by
  have eq : D.stock.rows.map (fun row=>row.key.length+row.multiplicity.val.length)=
      D.stock.rows.map (fun _=>(A+1+q)) := by
    apply List.map_congr_left
    intro x hx
    rw [D.roster.words x hx,x.multiplicity.property]
  unfold rawStockBits
  rw [D.stock.margin.property,eq]
  have widths (rs : List (RawCentre q)) : (rs.map (fun _=>(A+1+q))).sum=(A+1+q)*rs.length := by
    induction rs with
    | nil => simp
    | cons _ xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.mul_succ]
      omega
  rw [widths]

theorem stock_sweep_rows_bounded_by_actual_printed_grid
    {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {bank : Bank f}
    (D : Schedule sel d bank q) :
    D.stock.rows.length ≤ 2^(A+1) := by
  have same : D.proofView.centres.length=D.stock.rows.length := by
    change D.centresView.length=_
    simp only [Schedule.centresView,List.length_pmap]
  rw [←same]
  exact retained_centre_count_le_grid D.proofView

include T in
theorem actual_sweep_stock_grid_and_shape_fit
    (p : Path sel r c) (on : (S).cutoff<c.edges) (K : ℕ)
    (cs : PrintedCentreScale s C K) :
    A+1 ≤ K ∧ U ≤ K ∧ 2^(A+1) ≤ K := by
  have dim : A ≤ Nat.clog 2 s := bits_le_lam _ _
  have grid : 2^(A+1) ≤ K :=
    (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ dim)).trans
      ((Nat.le_add_right _ 1).trans cs.centreSlots)
  have scale : C*s ≤ K := (Nat.le_mul_of_pos_left _ (by decide : 0<(4:ℕ))).trans cs.edges
  have span := (actual_path_taper T p on).2.trans
    ((physical_edges_at_most_root_scale (cfg:=cfg) p T.rootStable).trans scale)
  have grow (i : ℕ) : i+1 ≤ 2^(i+1) := by
    induction i with
    | zero => decide
    | succ i ih =>
      rw [show i.succ+1=(i+1)+1 by omega,pow_succ]
      omega
  exact ⟨(grow A).trans grid,span,grid⟩

theorem true_sweep_selected_tapes_and_probes_are_bounded
    (p : Path sel r c) (on : (S).cutoff<c.edges) (hq : 0<q)
    (F : InputFits sel (readyAtPath T p on) q) (chart : MaskTable f.natDegree n good)
    (cover : physicalProbeCount f ell s c ≤ n)
    (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel (readyAtPath T p on) cw))
    (K : ℕ) (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) (wp : pw ≤ K) (we : ew ≤ K) :
    let taper := actual_path_taper T p on
    let D := (prepare (bank:=T.bank) hq F taper.1 taper.2 hf chart cover W L).result
    rawStockBits D.stock ≤ K+(K+K)*K ∧
    (∀ t, ((D.proofView.tape t).tape).steps ≤ preparedCentrePx K) ∧
    (∀ t z, ((D.proofView.tape t).masks z).steps ≤ mountedMaskPx K) := by
  let taper := actual_path_taper T p on
  let d := readyAtPath T p on
  let D := (prepare (bank:=T.bank) hq F taper.1 taper.2 hf chart cover W L).result
  have hs := actual_sweep_stock_grid_and_shape_fit (T:=T) p on K cs
  have rows := (stock_sweep_rows_bounded_by_actual_printed_grid D).trans hs.2.2
  have one := hs.1
  have hm := ws.modeWord
  have field : f.natDegree ≤ K := by simpa only [cfg.coefficient] using ws.field
  have obs (x : D.EmitRow) :=
    prepare_at_emitted_row_keeps_true_paid_tape_and_probe (bank:=T.bank) hq F
      taper.1 taper.2 hf chart cover W L x
  refine ⟨?_,?_,?_⟩
  · rw [exact_sweep_stock_width D]
    exact Nat.add_le_add hm (Nat.mul_le_mul (Nat.add_le_add one hm) rows)
  · intro t
    obtain ⟨x,hx⟩ := D.tag_surj t
    subst t
    change (D.proofCentre (D.tag x)).tape.steps ≤ _
    rw [D.proofCentre_on_emission]
    let t := D.tag x
    let copy := copyOfLayout q L.result
    let law := (retained_layout_copy_word L.result F.copies).1
    let I := centreWords hq F taper.1 taper.2 W.result copy.result law t
    have earlier := paid_tape_at_actual_path T p on t hq (F.axis t) I K ws cs
    have controlWord := (centre_precision_from_shared_words hq d t W.result taper.1 taper.2 (F.register t)).2
    change (centrePrecision hq d t W.result).steps ≤ _ at controlWord
    have aK : A ≤ K := (Nat.le_succ A).trans one
    have ctrl := actual_fixed_word_control_roof wp we hm aK hs.2.1
    have iCap : I.steps ≤ ctrlFee K K K K K+3 :=
      Nat.add_le_add_right (controlWord.trans ctrl) 3
    have native : (paidTape hq (F.axis t) I).steps ≤ liveActiveTapeRoof K :=
      earlier.trans (Nat.add_le_add_right iCap _)
    have eraseBound : (10*(A+1)+5)*D.stock.rows.length+6 ≤ nthRowAddonPx K :=
      Nat.add_le_add_right (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left _ one) _) rows) 6
    rw [(obs x).2.1]
    change (paidTape hq (F.axis t) I).steps+(10*(A+1)+5)*D.stock.rows.length+3+3 ≤ _
    exact (by
      unfold preparedCentrePx
      have b := Nat.add_le_add native eraseBound
      omega)
  · intro t z
    obtain ⟨x,hx⟩ := D.tag_surj t
    subst t
    change ((D.proofCentre (D.tag x)).masks z).steps ≤ _
    rw [D.proofCentre_on_emission,((obs x).2.2 z).2]
    unfold mountedMaskPx
    have nProbe := (actual_centre_dimension_fields (cfg:=cfg) p T.rootStable on (D.tag x)).2.2.1.trans cs.probes
    exact Nat.mul_le_mul ((Nat.succ_le_of_lt z.isLt).trans nProbe)
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ field) _)
theorem original_sweep_frame_dimensions
    (p : Path sel r c) (on : (S).cutoff < c.edges) (hq : 0<q)
    (F : InputFits sel (readyAtPath T p on) q) (chart : MaskTable f.natDegree n good)
    (cover : physicalProbeCount f ell s c ≤ n)
    (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel (readyAtPath T p on) cw))
    (K : ℕ) (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K)
    (absoluteHigh : absolutePrecision s r.edges r.prec+
        (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)) ≤ K) :
    let taper := actual_path_taper T p on
    let D := (prepare (bank:=T.bank) hq F taper.1 taper.2 hf chart cover W L).result
    ell ≤ K ∧ q ≤ K ∧ c.prec+D.extra ≤ K ∧
      (∀ x : D.EmitRow, let t := D.tag x; let J := D.fetch x;
        registerPrecision S c t ≤ K ∧ J.low.words.length ≤ K ∧ J.window ≤ K ∧
          physicalProbeCount f ell s c ≤ K ∧ J.roster.rows.length+1 ≤ K ∧
          J.tape.result.words.length ≤ K) := by
  let taper := actual_path_taper T p on
  let D := (prepare (bank:=T.bank) hq F taper.1 taper.2 hf chart cover W L).result
  have dim : A ≤ Nat.clog 2 s := J6R16ModeCost.bits_le_lam _ _
  have highEq : D.extra=commonLoss A c.edges U :=
    (prepare_uses_captured_inputs_once (bank:=T.bank) hq F taper.1 taper.2 hf chart cover W L).2.1
  have hEdges := physical_edges_at_most_root_scale (cfg:=cfg) p T.rootStable
  have hLoss := (simple_common_scale_cap dim taper.1 taper.2).trans (Nat.mul_le_mul_right _ hEdges)
  have hPrec := absolute_inherited_precision_cap cfg sel T.rootStable p
  refine ⟨ws.baseV,ws.modeWord,?_,?_⟩
  · change c.prec+D.extra ≤ K
    rw [highEq]
    exact (Nat.add_le_add hPrec hLoss).trans absoluteHigh
  · intro x
    let t := D.tag x
    let J := D.fetch x
    have param := actual_centre_dimension_fields (cfg:=cfg) p T.rootStable on t
    have field : f.natDegree ≤ K := by simpa only [cfg.coefficient] using ws.field
    have sz : J.roster.rows.length+1 ≤ K :=
      (Nat.add_le_add_right (J.roster.length_le_grid.trans
        (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ dim))) 1).trans cs.centreSlots
    exact ⟨param.2.2.2.2.2.1.trans ws.register,(J.low.natDegree hf).le.trans field,
      param.2.2.2.1.trans cs.edges,param.2.2.1.trans cs.probes,sz,
      (actual_weight_words_at_absolute_scale (cfg:=cfg) p T.rootStable J.tape.result).trans ws.weightTape⟩

end

#print axioms stock_admission_from_actual_dimensions
#print axioms exact_sweep_stock_width
#print axioms stock_sweep_rows_bounded_by_actual_printed_grid
#print axioms actual_sweep_stock_grid_and_shape_fit
#print axioms true_sweep_selected_tapes_and_probes_are_bounded
#print axioms original_sweep_frame_dimensions
end J6R68ActiveInputs.Sweep
