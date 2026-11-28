import P6JointWeights

namespace Paper6JointSeating
open scoped BigOperators
open P11FullPacking P9BalancedChart GuardedPacking

set_option maxHeartbeats 3000000 in
theorem joint_from_matching
    {W K R E : Type*} [Fintype W] [DecidableEq W] [LinearOrder K] [Fintype K]
    [Fintype E] [DecidableEq E] {a b : ℕ} (ha : 0<a)
    (label : W → Cell (Fin a) K) (row : W → R) (own : W → E)
    (clones matched nonpins : Finset W)
    (clonesNonpin : clones ⊆ nonpins) (matchesNonpin : matched ⊆ nonpins)
    (rowC : Set.InjOn row {w | w ∈ clones}) (rowM : Set.InjOn row {w | w ∈ matched})
    (sameOwner : ∀ x y, row x = row y → own x = own y)
    (portCap : ∀ e, (clones.filter (fun w => own w = e)).card ≤ 3)
    (matchCap : ∀ e, (matched.filter (fun w => own w = e)).card ≤ 3)
    (cap : ∀ c, Nat.card (RealFiber label c) ≤ b*2^a)
    (poolBound : ∀ c, 2*b ≤ (ofCell label nonpins c).card)
    (B : ℝ) (hB : 0≤B)
    (estimate : (2*(Fintype.card E : ℝ) + 9*(Fintype.card W : ℝ))/(2^a:ℕ) ≤ B)
    (margin : ∀ c, 2*(b:ℝ)+(ofCell label matched c).card/(2^a:ℕ)+Real.sqrt B
      ≤ (ofCell label matched c).card) :
    ∃ (seat : W ↪ Physical a b K) (keep : Bool → Finset E),
      Disjoint (keep false) (keep true) ∧
      (∀ s, (Fintype.card E : ℝ)/(2^a:ℕ) ≤ (keep s).card +
        Real.sqrt B + Real.sqrt ((Fintype.card (Cell (Fin a) K) : ℝ)*B)) ∧
      (∀ w, physicalCell (balancedMask a b K) (seat w) = label w) ∧
      (∀ w s, w ∈ clones → own w ∈ keep s → (seat w).2 = endpointIndex a s) ∧
      (∀ z s, z.2 = endpointIndex a s → ∃ w, seat w = z) ∧
      (∀ w s, (seat w).2 = endpointIndex a s → w ∈ nonpins) ∧
      Set.InjOn row {w | (seat w).2 = endpointIndex a false} := by
  classical
  let L : ℕ := 2^a
  have hL : 2 ≤ L := (pow_one 2).symm.trans_le (Nat.pow_le_pow_right (by decide) ha)
  let p := weights label own clones
  let k := weights label own matched
  have capP (c) : (cellLoad p Finset.univ c : ℝ)/L ≤ b := by
    rw [show cellLoad p Finset.univ c = (ofCell label clones c).card by exact load_univ _ _ _ _]
    apply (div_le_iff₀ (by positivity)).mpr
    have hcl : (ofCell label clones c).card ≤ Nat.card (RealFiber label c) := by
      let emb : {w // w ∈ ofCell label clones c} ↪ RealFiber label c :=
        ⟨fun w => ⟨w.val,(Finset.mem_filter.mp w.prop).2⟩,
          fun _ _ h => Subtype.ext (congrArg (fun x : RealFiber label c => x.val) h)⟩
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Nat.card_le_card_of_injective emb emb.injective
    exact_mod_cast hcl.trans (cap c)
  have variance (s : Finset W) (h : ∀ e, (s.filter (fun w => own w = e)).card ≤ 3) :
      (∑ c, ∑ e, (weights label own s e c : ℝ)^2) ≤ 3*(Fintype.card W : ℝ) := by
    apply (variance_le label own s 3 ?_).trans
    · have hcard := Finset.card_le_card (Finset.subset_univ s)
      rw [Finset.card_univ] at hcard
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by norm_num)
    · intro e c
      apply le_trans _ (h e)
      exact Finset.card_le_card (fun w hw => by
        have g := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp g.1).1,g.2⟩)
  have var : ((Fintype.card E : ℝ)*2 + 2*(∑ c, ∑ e, (p e c : ℝ)^2) +
        (∑ c, ∑ e, (k e c : ℝ)^2)) / L ≤ B := by
    apply le_trans _ estimate
    apply div_le_div_of_nonneg_right _ (by positivity)
    change _ ≤ 2*(Fintype.card E : ℝ) + 9*(Fintype.card W : ℝ)
    linarith [variance clones portCap,variance matched matchCap]
  obtain ⟨keep,hd,hks,hconf⟩ := select_with_conflict hL false p k (fun _ => b) capP B hB var
  let r (s : Bool) (c) := (ofCell label clones c).filter (fun w => own w ∈ keep s)
  let t0 (c) := (ofCell label matched c).filter (fun w => own w ∈ keep false)
  let f0 (c) := ofCell label matched c \ (t0 c ∪ r true c)
  have rcap (s c) : (r s c).card ≤ b := by
    rw [← load_filter]
    exact (hks s).1 c
  have fcap (c) : b - (r false c).card ≤ (f0 c).card := by
    have hc : ((t0 c).card : ℝ) ≤ (ofCell label matched c).card/L+Real.sqrt B := by
      simpa only [t0, ← load_filter, load_univ, k] using hconf c
    have hm := margin c
    have hc' : 2*b+(t0 c).card ≤ (ofCell label matched c).card := by
      exact_mod_cast (show 2*(b:ℝ)+((t0 c).card:ℝ) ≤ (ofCell label matched c).card by linarith)
    have hi : (ofCell label matched c ∩ (t0 c ∪ r true c)).card ≤
        (t0 c ∪ r true c).card := Finset.card_le_card Finset.inter_subset_right
    have hu := Finset.card_union_le (t0 c) (r true c)
    have hv := Finset.card_sdiff_add_card_inter (s:=ofCell label matched c) (t:=t0 c ∪ r true c)
    have hrc := rcap true c
    dsimp [f0]
    omega
  have useR (w : W) (s : Bool) (c) (h : w ∈ r s c) :
      w ∈ clones ∧ label w=c ∧ own w ∈ keep s := by
    have h' := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_filter.mp h'.1).1,(Finset.mem_filter.mp h'.1).2,h'.2⟩
  have useF (w : W) (c) (h : w ∈ f0 c) :
      w ∈ matched ∧ label w=c ∧ own w ∉ keep false ∧ w ∉ r true c := by
    have h' := Finset.mem_sdiff.mp h
    have h'' := Finset.mem_filter.mp h'.1
    refine ⟨h''.1,h''.2,?_,fun hx => h'.2 (Finset.mem_union_right _ hx)⟩
    exact fun hj => h'.2 (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h'.1,hj⟩))
  have hl (c w) : w ∈ r false c ∨ w ∈ r true c ∨ w ∈ f0 c ∨ w ∈ ofCell label nonpins c →
      label w=c ∧ w ∈ nonpins := by
    rintro (hr|hr|hp|hn)
    · exact ⟨(useR w false c hr).2.1,clonesNonpin (useR w false c hr).1⟩
    · exact ⟨(useR w true c hr).2.1,clonesNonpin (useR w true c hr).1⟩
    · exact ⟨(useF w c hp).2.1,matchesNonpin (useF w c hp).1⟩
    · exact ⟨(Finset.mem_filter.mp hn).2,(Finset.mem_filter.mp hn).1⟩
  have rd (c) : Disjoint (r false c) (r true c) :=
    Finset.disjoint_left.mpr (fun w hx hy => Finset.disjoint_left.mp hd
      (useR w false c hx).2.2 (useR w true c hy).2.2)
  have av0 (c) : Disjoint (r false c) (f0 c) :=
    Finset.disjoint_left.mpr (fun w hx hy => (useF w c hy).2.2.1 (useR w false c hx).2.2)
  have av1 (c) : Disjoint (r true c) (f0 c) :=
    Finset.disjoint_left.mpr (fun w hx hy => (useF w c hy).2.2.2 hx)
  have hi : Set.InjOn row {w | w ∈ r false (label w)} :=
    fun x hx y hy => rowC (useR x false _ hx).1 (useR y false _ hy).1
  have hj : Set.InjOn row {w | w ∈ f0 (label w)} :=
    fun x hx y hy => rowM (useF x _ hx).1 (useF y _ hy).1
  have gap : ∀ x y, x ∈ r false (label x) → y ∈ f0 (label y) → row x ≠ row y := by
    intro x y hx hy hxy
    apply (useF y _ hy).2.2.1
    rw [← sameOwner x y hxy]
    exact (useR x false _ hx).2.2
  obtain ⟨seat,hs,hzero,hend,hfilled,hpin,hrow⟩ := reserveAndPlace ha label row
    (fun w => w ∈ nonpins) (r false) (r true) f0 (ofCell label nonpins)
    cap (rcap false) (rcap true) fcap poolBound hl rd av0 av1 hi hj gap
  refine ⟨seat,keep,hd,fun s => (hks s).2,hs,?_,hfilled,hpin,hrow⟩
  intro w s hw hk
  have hr : w ∈ r s (label w) := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hw,rfl⟩, hk⟩
  cases s
  · exact hzero w hr
  · exact hend w hr

#print axioms joint_from_matching
end Paper6JointSeating

