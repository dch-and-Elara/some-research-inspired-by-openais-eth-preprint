import P6JointMarking

namespace Paper6JointSeating
open scoped BigOperators
open GuardExpectation GuardedPacking

variable {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C]

private abbrev Stats (C : Type*) := (Bool × Option C) ⊕ C

private def side (pos : Bool) : Stats C → Bool
  | .inl i => i.1
  | .inr _ => pos

private def load (p k : E → C → ℕ) : Stats C → E → ℕ
  | .inl (_, .none) => fun _ => 1
  | .inl (_, .some c) => fun e => p e c
  | .inr c => fun e => k e c

set_option maxHeartbeats 1200000 in
theorem select_with_conflict
    {L : ℕ} (hL : 2 ≤ L) (pos : Bool)
    (p k : E → C → ℕ) (b : C → ℕ)
    (capacity : ∀ c, ((cellLoad p Finset.univ c : ℕ) : ℝ) / L ≤ b c)
    (B : ℝ) (hB : 0 ≤ B)
    (var : ((Fintype.card E : ℝ)*2 + 2*(∑ c, ∑ e, (p e c : ℝ)^2) +
        (∑ c, ∑ e, (k e c : ℝ)^2)) / L ≤ B) :
    ∃ keep : Bool → Finset E,
      Disjoint (keep false) (keep true) ∧
      (∀ s, (∀ c, cellLoad p (keep s) c ≤ b c) ∧
        (Fintype.card E : ℝ)/L ≤ (keep s).card +
          Real.sqrt B + Real.sqrt ((Fintype.card C : ℝ)*B)) ∧
      ∀ c, (cellLoad k (keep pos) c : ℝ) ≤
        (cellLoad k Finset.univ c : ℝ)/L + Real.sqrt B := by
  classical
  obtain ⟨a,ha⟩ := uniform_joint_potential (E:=E) (I:=Stats C) hL
    (side pos) (fun i e => (load p k i e : ℚ))
  let m := fun s => markedSet a (signSymbol L hL s)
  let dev : Stats C → ℝ := fun i => (centeredLoad (L : ℚ)⁻¹
    (signSymbol L hL (side pos i)) (fun e => (load p k i e : ℚ)) a : ℚ)
  have hsq : (∑ i, dev i ^ 2) ≤ B := by
    have ha' := (Rat.cast_le (K:=ℝ)).mpr ha
    push_cast at ha'
    change (∑ i, dev i ^ 2) ≤ _ at ha'
    apply ha'.trans
    have hexpand : (∑ i : Stats C, ∑ e, (load p k i e : ℝ)^2) =
        (Fintype.card E : ℝ)*2 + 2*(∑ c, ∑ e, (p e c : ℝ)^2) +
           (∑ c, ∑ e, (k e c : ℝ)^2) := by
      simp [Stats, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_option,
        load]
      ring
    rw [hexpand]
    apply le_trans _ var
    rw [div_eq_mul_inv, mul_comm _ ((L : ℝ)⁻¹), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_of_le_one_left (by positivity) (by
      linarith [show (0 : ℝ) ≤ (L : ℝ)⁻¹ by positivity])
  have hcount (s : Bool) :
      dev (.inl (s, none)) = ((m s).card : ℝ) - (Fintype.card E : ℝ)/L := by
    have h := centered_count a (signSymbol L hL s)
    simpa [dev,side,load,m] using congrArg (fun z : ℚ => (z : ℝ)) h
  have hcell (s : Bool) (c : C) : dev (.inl (s, some c)) =
      (cellLoad p (m s) c : ℝ) - (cellLoad p Finset.univ c : ℝ)/L := by
    have h := centered_cell a (signSymbol L hL s) p c
    simpa [dev,side,load,m] using congrArg (fun z : ℚ => (z : ℝ)) h
  have hconf (c : C) : dev (.inr c) =
      (cellLoad k (m pos) c : ℝ) - (cellLoad k Finset.univ c : ℝ)/L := by
    have h := centered_cell a (signSymbol L hL pos) k c
    simpa [dev,side,load,m] using congrArg (fun z : ℚ => (z : ℝ)) h
  have one (i : Stats C) : dev i ^ 2 ≤ B :=
    (Finset.single_le_sum (fun i _ => sq_nonneg (dev i)) (Finset.mem_univ i)).trans hsq
  have cells (s : Bool) : (∑ c, dev (.inl (s, some c)) ^ 2) ≤ B := by
    apply le_trans _ hsq
    let f : C → Stats C := fun c => Sum.inl (s, some c)
    have hinj : Function.Injective f := by intro x y h; simpa [f] using h
    change (∑ c, dev (f c)^2) ≤ _
    calc
      (∑ c, dev (f c)^2) = ∑ i ∈ Finset.univ.image f, dev i^2 := by
        symm
        exact Finset.sum_image (fun _ _ _ _ h => hinj h)
      _ ≤ ∑ i, dev i^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => sq_nonneg (dev i))
  have build (s : Bool) : ∃ t : Finset E, t ⊆ m s ∧
      (∀ c, cellLoad p t c ≤ b c) ∧
      (Fintype.card E : ℝ)/L ≤ t.card + Real.sqrt B +
        Real.sqrt ((Fintype.card C : ℝ)*B) := by
    have hc := one (.inl (s,none))
    rw [hcount, ← neg_sq] at hc
    have ht := squareDeviation_le_sqrt hc hB
    have hcells := cells s
    simp only [hcell] at hcells
    obtain ⟨t,hts,htb,htc⟩ := retain_from_deviations p b (m s)
      (fun c => (cellLoad p Finset.univ c : ℝ)/L) capacity B hB hcells
    refine ⟨t,hts,htb,?_⟩
    linarith
  choose keep hsub hcap hn using build
  have hd := disjoint_markedSet a ((signSymbol_injective L hL).ne (by decide : false ≠ true))
  refine ⟨keep,Finset.disjoint_left.mpr ?_,fun s => ⟨hcap s, hn s⟩,?_⟩
  · intro e hs ht
    exact Finset.disjoint_left.mp hd (hsub false hs) (hsub true ht)
  · intro c
    have h1 := one (.inr c)
    rw [hconf] at h1
    have ht := squareDeviation_le_sqrt h1 hB
    have hk := cellLoad_mono (hsub pos) (w:=k) (c:=c)
    have hkr : (cellLoad k (keep pos) c : ℝ) ≤ (cellLoad k (m pos) c : ℝ) := by exact_mod_cast hk
    linarith

#print axioms select_with_conflict
end Paper6JointSeating


