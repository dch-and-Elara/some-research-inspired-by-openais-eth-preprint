import J2R47P9ZeroProbeReserve

/-! The original P9 endpoint guard and the extra reservations have a
single real balanced physical seat injection, with +6 census loss. -/
namespace J2R47P9ZeroProbe
open scoped Classical BigOperators
open P11FullPacking P9BalancedChart GuardedPacking OuterNodePacking
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option maxRecDepth 2000
set_option linter.unusedSectionVars false
noncomputable section

variable {U K : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable [LinearOrder K] [Fintype K] {a b : ℕ}

theorem guarded_real_layout_with_reservations (ha : 0<a) (hb : 4≤b)
    (label : U→Bool→Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber (fun w : U×Bool=>label w.1 w.2) c)≤b*2^a)
    (res : Bool→Finset U) (hres : Disjoint (res false) (res true))
    (size : ∀ s,(res s).card≤2) :
    ∃ seat : U×Bool↪Physical a b K,
      (∀ w, physicalCell (balancedMask a b K) (seat w)=label w.1 w.2) ∧
      (∀ s u, u∈res s → ∀ p,(seat (u,p)).2=endpointIndex a s) ∧
      ∀ (packets : Finset (Page a b K)) (t : ℤ), t≠0 →
        (Fintype.card U:ℝ)/(2^a:ℕ) ≤
        ((untouched Finset.univ (vertexOwner seat)
          (matchedColumns packets (realSlot seat) (realSlot seat) t)).card:ℝ) +
        Real.sqrt (5*(2*(Fintype.card U:ℝ))/(2^a:ℕ)) +
        Real.sqrt ((Fintype.card (Cell (Fin a) K):ℝ) *
          (5*(2*(Fintype.card U:ℝ))/(2^a:ℕ))) + 6 := by
  classical
  have hL : 2≤2^a := (pow_one 2).symm.trans_le (Nat.pow_le_pow_right (by decide) ha)
  have cellMean (c : Cell (Fin a) K) :
      ((cellLoad (GuardedPacking.multiplicity label) Finset.univ c:ℕ):ℝ)/(2^a:ℕ)≤b := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := cap c
    rw [Nat.card_congr (wholeFiberEquiv label c),Nat.card_eq_fintype_card,card_markedPort] at hh
    exact_mod_cast hh
  obtain ⟨inKeep,inDis,inFits⟩ := select_capacity hL label b cellMean
  have resFits (s : Bool) (c : Cell (Fin a) K) :
      cellLoad (GuardedPacking.multiplicity label) (res s) c≤b := by
    have h := Finset.single_le_sum
      (f:=fun c : Cell (Fin a) K=>cellLoad (GuardedPacking.multiplicity label) (res s) c)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ c)
    rw [total_two_port_load] at h
    change cellLoad (GuardedPacking.multiplicity label) (res s) c≤2*(res s).card at h
    have n := size s
    omega
  obtain ⟨out,dis,outFits⟩ := protect_reservations label b inKeep res inDis hres
    (fun s=>(inFits s).1) resFits
  have smallLoss (s : Bool) : (inKeep s).card≤(out s).card+6 := by
    have hc := (outFits s).2.2
    rw [Finset.card_union_of_disjoint hres] at hc
    have a := size false
    have b := size true
    have hs := size s
    omega
  have outMarked (c : Cell (Fin a) K) (s : Bool) :
      Nat.card (Marked (fun w : U×Bool => label w.1 w.2) (signedMark out) c s)≤b := by
    rw [Nat.card_congr (markedFiberEquiv label c out dis s),Nat.card_eq_fintype_card,card_markedPort]
    exact (outFits s).2.1 c
  obtain ⟨seat,labelOk,endOk⟩ := place_all ha (fun w : U×Bool=>label w.1 w.2)
    (signedMark out) cap outMarked
  have endAll (s : Bool) (u : U) (h : u∈out s) (p : Bool) :
      (seat (u,p)).2=endpointIndex a s :=
    endOk (u,p) s ((marked_iff out dis (u,p) s).mpr h)
  refine ⟨seat,labelOk,(fun s u hu p=>endAll s u ((outFits s).1 hu) p),?_⟩
  intro packets t ht
  have side (s : Bool) : (out s).card≤
      (P11SourceGeometry.seated Finset.univ (fun u p=>seat (u,p)) s).card := by
    apply Finset.card_le_card
    intro u hu
    apply (P11SourceGeometry.mem_seated _ _ _ _).mpr
    exact ⟨Finset.mem_univ _,fun p=>congrArg Fin.val (endAll s u hu p)⟩
  have hAll := P11SourceGeometry.both_endpoint_counts_le_every_shift
    (Finset.univ : Finset U) packets (fun e p=>seat (e,p))
    (realSlot seat) (realSlot seat) (vertexOwner seat) (real_fullPortFiber seat) t ht
  have h := (min_le_min (side false) (side true)).trans hAll
  have bound (s : Bool) (fits : (out s).card≤
      (untouched Finset.univ (vertexOwner seat)
        (matchedColumns packets (realSlot seat) (realSlot seat) t)).card) :
      (Fintype.card U:ℝ)/(2^a:ℕ) ≤
        ((untouched Finset.univ (vertexOwner seat)
          (matchedColumns packets (realSlot seat) (realSlot seat) t)).card:ℝ) +
        Real.sqrt (5*(2*(Fintype.card U:ℝ))/(2^a:ℕ)) +
        Real.sqrt ((Fintype.card (Cell (Fin a) K):ℝ) *
          (5*(2*(Fintype.card U:ℝ))/(2^a:ℕ))) + 6 := by
    have h1 := (inFits s).2
    have h2 : ((inKeep s).card:ℝ)≤(out s).card+6 := by exact_mod_cast smallLoss s
    have h3 : ((out s).card:ℝ)≤
      ((untouched Finset.univ (vertexOwner seat)
        (matchedColumns packets (realSlot seat) (realSlot seat) t)).card:ℝ) := by
      exact_mod_cast fits
    linarith only [h1,h2,h3]
  by_cases hs : (out false).card≤(out true).card
  · rw [min_eq_left hs] at h
    exact bound false h
  · rw [min_eq_right (le_of_not_ge hs)] at h
    exact bound true h

#print axioms guarded_real_layout_with_reservations
end
end J2R47P9ZeroProbe

