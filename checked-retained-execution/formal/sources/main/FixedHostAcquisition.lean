import Acquisition

/-!
# A2: a fixed physical host for input-dependent exact counting

Only one truth-table entry per potential edge is allowed to vary. Equality
chains, vertex occurrences, pinned auxiliaries, the two-wire physical
doubling and the specified shifted register are independent of those bits.
The packet placement remains a separate finite certificate.
-/

open scoped BigOperators

namespace FixedHostAcquisition

open Acquisition

abbrev Vertex (n : ℕ) := Fin (n + 1)
abbrev Pair (n : ℕ) := { p : Vertex n × Vertex n // p.1 < p.2 }
abbrev Occurrence (n : ℕ) := Vertex n × Vertex n
abbrev Link (n : ℕ) := Vertex n × Fin n
abbrev Auxiliary (n : ℕ) := Link n × Bool

abbrev Row (n : ℕ) := Pair n ⊕ Link n
abbrev Column (n : ℕ) := Occurrence n ⊕ Auxiliary n

/-- Two ports for a pair, and data/auxiliary × two endpoints for a link. -/
def WireAt {n : ℕ} : Row n → Type
  | .inl _ => Bool
  | .inr _ => Bool × Bool

instance {n : ℕ} (r : Row n) : Fintype (WireAt r) :=
  match r with
  | .inl _ => inferInstanceAs (Fintype Bool)
  | .inr _ => inferInstanceAs (Fintype (Bool × Bool))

instance {n : ℕ} (r : Row n) : DecidableEq (WireAt r) :=
  match r with
  | .inl _ => inferInstanceAs (DecidableEq Bool)
  | .inr _ => inferInstanceAs (DecidableEq (Bool × Bool))

abbrev Wire (n : ℕ) := Σ r : Row n, WireAt r

def pairOccurrence {n : ℕ} (p : Pair n) : Bool → Occurrence n
  | false => p.1
  | true => (p.1.2, p.1.1)

def stepOccurrence {n : ℕ} (l : Link n) : Bool → Occurrence n
  | false => (l.1, l.2.castSucc)
  | true => (l.1, l.2.succ)

/-- Public incidence map. Input switch settings do not enter this definition. -/
def owner {n : ℕ} : Wire n → Column n
  | ⟨.inl p, b⟩ => .inl (pairOccurrence p b)
  | ⟨.inr l, p⟩ =>
      if p.2 then .inr (l,p.1) else .inl (stepOccurrence l p.1)

def auxPort {n : ℕ} (p : Auxiliary n) : Wire n := ⟨.inr p.1, (p.2,true)⟩

@[simp] theorem owner_auxPort {n : ℕ} (p : Auxiliary n) : owner (auxPort p) = .inr p := by
  cases p
  rfl

theorem owner_onto {n : ℕ} (hn : 0 < n) : Function.Surjective (owner (n := n)) := by
  intro c
  cases c with
  | inr aux => exact ⟨auxPort aux, owner_auxPort aux⟩
  | inl occurrence =>
    rcases occurrence with ⟨v,j⟩
    by_cases hzero : j = 0
    · let i : Fin n := ⟨0, hn⟩
      have hij : i.castSucc = j := by
        rw [hzero]
        rfl
      refine ⟨⟨.inr (v,i), (false,false)⟩, ?_⟩
      change Sum.inl (v, i.castSucc) = Sum.inl (v,j)
      rw [hij]
    · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hzero
      exact ⟨⟨.inr (v,i), (true,false)⟩, rfl⟩

theorem wire_card {n : ℕ} :
    Fintype.card (Wire n) = 2 * Fintype.card (Pair n) + 4 * Fintype.card (Link n) := by
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  simp [WireAt, mul_comm]

theorem physical_wire_bound {n : ℕ} : Fintype.card (Wire n × Bool) ≤ 12 * (n+1)^2 := by
  have hPair : Fintype.card (Pair n) ≤ (n+1)^2 := by
    simpa [Pair, pow_two] using
      (Fintype.card_le_of_injective (Subtype.val : Pair n → Vertex n × Vertex n) Subtype.val_injective)
  have hLink : Fintype.card (Link n) ≤ (n+1)^2 := by
    simp only [Link, Vertex, Fintype.card_prod, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul_left _ (Nat.le_succ n)
  rw [Fintype.card_prod, Fintype.card_bool, wire_card]
  omega

theorem pairOccurrence_injective {n : ℕ} :
    Function.Injective (fun e : Pair n × Bool => pairOccurrence e.1 e.2) := by
  intro ⟨p,b⟩ ⟨q,c⟩ h
  cases b <;> cases c
  · exact Prod.ext (Subtype.ext h) rfl
  · change p.1 = (q.1.2,q.1.1) at h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    have bad := p.2
    rw [h₁, h₂] at bad
    exact (lt_asymm q.2 bad).elim
  · change (p.1.2,p.1.1) = q.1 at h
    have h₁ := congrArg Prod.fst h.symm
    have h₂ := congrArg Prod.snd h.symm
    have bad := q.2
    rw [h₁, h₂] at bad
    exact (lt_asymm p.2 bad).elim
  · change (p.1.2,p.1.1) = (q.1.2,q.1.1) at h
    exact Prod.ext (Subtype.ext (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))) rfl

theorem stepOccurrence_injective {n : ℕ} (b : Bool) :
    Function.Injective (fun l : Link n => stepOccurrence l b) := by
  intro ⟨v,i⟩ ⟨w,j⟩ h
  cases b
  · change (v,i.castSucc) = (w,j.castSucc) at h
    refine Prod.ext ?_ ?_
    · exact congrArg (fun q : Occurrence n => q.1) h
    apply Fin.ext
    exact congrArg (fun q : Occurrence n => (q.2 : ℕ)) h
  · change (v,i.succ) = (w,j.succ) at h
    refine Prod.ext ?_ ?_
    · exact congrArg (fun q : Occurrence n => q.1) h
    apply Fin.ext
    have hi := congrArg (fun q : Occurrence n => (q.2 : ℕ)) h
    simp at hi
    exact hi

theorem auxPort_unique {n : ℕ} (c : Auxiliary n) {i : Wire n}
    (h : owner i = .inr c) : i = auxPort c := by
  rcases i with ⟨r,j⟩
  cases r with
  | inl p => simp [owner] at h
  | inr l =>
    rcases j with ⟨b,ctl⟩
    cases ctl with
    | false => simp [owner] at h
    | true =>
      have e : (l,b) = c := Sum.inr.inj h
      subst c
      rfl

/-- An occurrence is used at most once in each of the three categories:
one switched pair row, one predecessor copy, and one successor copy. -/
def occurrenceUsage {n : ℕ} : Wire n → Fin 3
  | ⟨.inl _, _⟩ => 0
  | ⟨.inr _, t⟩ => if t.1 then 2 else 1

theorem occurrenceUsage_injective {n : ℕ} (c : Occurrence n) :
    Function.Injective (fun p : {i : Wire n // owner i = .inl c} => occurrenceUsage p.1) := by
  intro ⟨⟨r,j⟩,h⟩ ⟨⟨s,k⟩,g⟩ e
  apply Subtype.ext
  cases r with
  | inl p =>
    cases s with
    | inl q =>
      have same : pairOccurrence p j = pairOccurrence q k := Sum.inl.inj (h.trans g.symm)
      exact congrArg (fun t : Pair n × Bool => (⟨.inl t.1,t.2⟩ : Wire n))
        (@pairOccurrence_injective n (p,j) (q,k) same)
    | inr l =>
      rcases k with ⟨b,ctl⟩
      have bad := congrArg Fin.val e
      cases b <;> simp [occurrenceUsage] at bad
  | inr l =>
    rcases j with ⟨b,ctl⟩
    cases ctl with
    | true => simp [owner] at h
    | false =>
      cases s with
      | inl p =>
        have bad := congrArg Fin.val e
        cases b <;> simp [occurrenceUsage] at bad
      | inr m =>
        rcases k with ⟨d,ctl⟩
        cases ctl with
        | true => simp [owner] at g
        | false =>
          have hd : d = b := by
            have e' := congrArg Fin.val e
            cases b <;> cases d <;> simp_all [occurrenceUsage]
          subst d
          have same : stepOccurrence l b = stepOccurrence m b := Sum.inl.inj (h.trans g.symm)
          obtain rfl := @stepOccurrence_injective n b l m same
          rfl

theorem fixed_column_degree {n : ℕ} (c : Column n) :
    Fintype.card {i : Wire n // owner i = c} ≤ 3 := by
  classical
  cases c with
  | inl c =>
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (occurrenceUsage_injective c)
  | inr q =>
    have h : Function.Injective (fun _ : {i : Wire n // owner i = Sum.inr q} => ()) := by
      intro v w _
      apply Subtype.ext
      exact (auxPort_unique q v.2).trans (auxPort_unique q w.2).symm
    exact (Fintype.card_le_of_injective _ h).trans (by decide)

theorem fixed_row_degree {n : ℕ} (r : Row n) : Fintype.card (WireAt r) ≤ 4 := by
  cases r with
  | inl p => change Fintype.card Bool ≤ 4; decide
  | inr l => change Fintype.card (Bool × Bool) ≤ 4; decide


section Ring

variable {K : Type*} [CommRing K]
variable {n : ℕ}

def switchTable (enabled : Bool) (Y : Bool → Bool) : K :=
  if enabled then nandTable Y else 1

/-- Exactly the address at which enabling a potential edge changes the table. -/
theorem switchTable_exact_difference (Y : Bool → Bool) :
    (switchTable (K := K) false Y - switchTable true Y) =
      if Y = (fun _ => true) then 1 else 0 := by
  classical
  have h : Y = (fun _ => true) ↔ Y false = true ∧ Y true = true := by
    constructor
    · intro h
      rw [h]
      exact ⟨rfl,rfl⟩
    · intro h
      funext b
      cases b
      · exact h.1
      · exact h.2
  by_cases h0 : Y false = true <;> by_cases h1 : Y true = true <;>
    simp [switchTable, nandTable, bit, h, h0, h1]

def copyTable (Y : Bool × Bool → Bool) : K :=
  if (Y (false,false) && Y (false,true)) = (Y (true,false) && Y (true,true)) then 1 else 0

def rowTable (enabled : Pair n → Bool) : (r : Row n) → (WireAt r → Bool) → K
  | .inl p, Y => switchTable (enabled p) Y
  | .inr _, Y => copyTable Y

theorem switch_extension (enabled : Bool) (x : Bool → Bool) :
    extension (switchTable (K := K) enabled) (fun b => -bit (x b)) = switchTable enabled x := by
  cases enabled
  · exact extension_one _
  · exact nandTable_extension x

def splitFour : (Bool × Bool → Bool) ≃ Bool × (Bool × (Bool × Bool)) where
  toFun r := (r (false,false), r (false,true), r (true,false), r (true,true))
  invFun p ij := if ij.1 then (if ij.2 then p.2.2.2 else p.2.2.1)
    else (if ij.2 then p.2.1 else p.1)
  left_inv r := by
    funext ij
    rcases ij with ⟨i,j⟩
    cases i <;> cases j <;> rfl
  right_inv p := by
    rcases p with ⟨a,b,c,d⟩
    rfl

theorem shiftedCopy (x : Bool → Bool) :
    extension (copyTable (K := K))
      (fun p : Bool × Bool => if p.2 then -1 else -bit (x p.1)) =
    if x false = x true then 1 else 0 := by
  let a : Bool × Bool → K := fun p => if p.2 then -1 else -bit (x p.1)
  let f : (Bool × Bool → Bool) → K := fun y => copyTable y * ∏ i, lag (y i) (a i)
  change (∑ y, f y) = _
  calc
    _ = ∑ p, f (splitFour.symm p) :=
      Fintype.sum_equiv splitFour f _ (fun y => congrArg f (splitFour.symm_apply_apply y).symm)
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      cases h0 : x false <;> cases h1 : x true <;>
        norm_num [f, a, splitFour, copyTable, Fintype.prod_prod_type, lag, bit, h0, h1]

/-- Finite chain equalities in the fixed logical host. -/
def coherent (x : Occurrence n → Bool) : Prop :=
  ∀ l : Link n, x (stepOccurrence l false) = x (stepOccurrence l true)

noncomputable instance (x : Occurrence n → Bool) : Decidable (coherent x) :=
  Classical.propDecidable _

def liftVertices (x : Vertex n → Bool) : Occurrence n → Bool := x ∘ Prod.fst

theorem coherent_iff (x : Occurrence n → Bool) :
    coherent x ↔ ∃ v : Vertex n → Bool, liftVertices v = x := by
  constructor
  · intro h
    refine ⟨fun v => x (v,0), ?_⟩
    funext p
    rcases p with ⟨v,j⟩
    change x (v,0) = x (v,j)
    induction j using Fin.induction with
    | zero => rfl
    | succ i hi =>
      exact hi.trans (h (v,i))
  · rintro ⟨v,rfl⟩ l
    rfl

theorem liftVertices_injective : Function.Injective (liftVertices (n := n)) := by
  intro x y h
  funext v
  exact congrFun h (v,0)

def IsIndependent (enabled : Pair n → Bool) (x : Vertex n → Bool) : Prop :=
  ∀ p : Pair n, enabled p = true → ¬ (x p.1.1 = true ∧ x p.1.2 = true)

noncomputable def count (enabled : Pair n → Bool) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Vertex n → Bool)).filter (IsIndependent enabled)).card

theorem count_le (enabled : Pair n → Bool) : count enabled ≤ 2^(n+1) := by
  classical
  unfold count
  simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Vertex n → Bool)))
    (p := IsIndependent enabled))

def PairAccepted (enabled : Pair n → Bool) (x : Occurrence n → Bool) (p : Pair n) : Prop :=
  enabled p = true → ¬ (x (pairOccurrence p false) = true ∧ x (pairOccurrence p true) = true)

instance (enabled : Pair n → Bool) (x : Occurrence n → Bool) (p : Pair n) :
    Decidable (PairAccepted enabled x p) := by
  unfold PairAccepted
  infer_instance

theorem switchTable_indicator (enabled : Pair n → Bool) (x : Occurrence n → Bool) (p : Pair n) :
    switchTable (K := K) (enabled p) (x ∘ pairOccurrence p) =
      if PairAccepted enabled x p then 1 else 0 := by
  by_cases hb : enabled p = true <;>
    cases ha : x (pairOccurrence p false) <;> cases hc : x (pairOccurrence p true) <;>
      simp [switchTable, nandTable, bit, PairAccepted, hb, ha, hc]

def logicalPairs (enabled : Pair n → Bool) (x : Occurrence n → Bool) : K :=
  ∏ p : Pair n, switchTable (enabled p) (x ∘ pairOccurrence p)

def logicalLinks (x : Occurrence n → Bool) : K :=
  ∏ l : Link n, if x (stepOccurrence l false) = x (stepOccurrence l true) then 1 else 0

theorem logicalLinks_indicator (x : Occurrence n → Bool) :
    logicalLinks (K := K) x = if coherent x then 1 else 0 := by
  classical
  by_cases h : coherent x
  · rw [if_pos h, logicalLinks]
    exact Finset.prod_eq_one fun l _ => if_pos (h l)
  · rw [if_neg h, logicalLinks]
    obtain ⟨l,hl⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)

theorem logicalPairs_indicator (enabled : Pair n → Bool) (x : Occurrence n → Bool) :
    logicalPairs (K := K) enabled x = if ∀ p, PairAccepted enabled x p then 1 else 0 := by
  classical
  by_cases h : ∀ p, PairAccepted enabled x p
  · rw [if_pos h, logicalPairs]
    exact Finset.prod_eq_one fun p _ => (switchTable_indicator enabled x p).trans (if_pos (h p))
  · rw [if_neg h, logicalPairs]
    obtain ⟨p,hp⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ p) ((switchTable_indicator enabled x p).trans (if_neg hp))

theorem logical_count (enabled : Pair n → Bool) :
    (∑ x : Occurrence n → Bool, logicalPairs (K := K) enabled x * logicalLinks x) =
      (count enabled : K) := by
  classical
  let accepts (X : Occurrence n → Bool) := coherent X ∧ ∀ p, PairAccepted enabled X p
  have hterm (X : Occurrence n → Bool) :
      logicalPairs (K := K) enabled X * logicalLinks X = if accepts X then 1 else 0 := by
    rw [logicalPairs_indicator, logicalLinks_indicator]
    by_cases h : coherent X
    · by_cases j : ∀ p, PairAccepted enabled X p
      · rw [if_pos h, if_pos j, if_pos (show accepts X from ⟨h,j⟩), one_mul]
      · rw [if_pos h, if_neg j, if_neg (fun H : accepts X => j H.2), zero_mul]
    · rw [if_neg h, if_neg (fun H : accepts X => h H.1), mul_zero]
  have filter_count :
      ((Finset.univ : Finset (Occurrence n → Bool)).filter accepts).card = count enabled := by
    unfold count
    symm
    apply Finset.card_bij (fun x _ => liftVertices x)
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(coherent_iff _).mpr ⟨x,rfl⟩, ?_⟩⟩
      exact (Finset.mem_filter.mp hx).2
    · exact fun x _ y _ h => liftVertices_injective h
    · intro X hX
      have h := (Finset.mem_filter.mp hX).2
      obtain ⟨x, rfl⟩ := (coherent_iff X).mp h.1
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩, rfl⟩
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simpa using congrArg (fun x : ℕ => (x : K)) filter_count

end Ring

section Physical

variable {K : Type*} [CommRing K]
variable {n : ℕ}

def auxPins (a : Auxiliary n → Bool) : K :=
  ∏ k : Auxiliary n, bit (a k)

theorem auxPins_indicator (a : Auxiliary n → Bool) :
    auxPins (K := K) a = if a = (fun _ => true) then 1 else 0 := by
  classical
  by_cases h : a = (fun _ => true)
  · subst a
    simp [auxPins, bit]
  · rw [if_neg h, auxPins]
    obtain ⟨k,hk⟩ := not_forall.mp (show ¬ ∀ k, a k = true from fun G => h (funext G))
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [bit,hk])

/-- The actual physical old column tables: are the incident bits equal,
and do the fixed singleton auxiliary columns carry one? -/
noncomputable def columnTable (X : Wire n → Bool) : K :=
  equalityTensor owner X * auxPins (X ∘ auxPort)

def pinnedColumns (x : Occurrence n → Bool) : Column n → Bool :=
  Sum.elim x (fun _ => true)

/-- Eliminates the physical old column sums without assuming the resulting
clauses or the correct count. All forced auxiliary assignments are singleton. -/
theorem column_elimination (hn : 0 < n) (f : (Wire n → Bool) → K) :
    (∑ X : Wire n → Bool, columnTable X * f X) =
      ∑ x : Occurrence n → Bool, f (pinnedColumns x ∘ owner) := by
  classical
  simp only [columnTable, mul_assoc]
  rw [equalityTensor_sum _ (owner_onto hn)]
  have pins (X : Column n → Bool) : auxPins (K := K) ((X ∘ owner) ∘ auxPort) =
      auxPins (X ∘ Sum.inr) := by
    apply congrArg auxPins
    funext q
    simp only [Function.comp_apply, owner_auxPort]
  simp_rw [pins]
  calc
    _ = ∑ Z : (Occurrence n → Bool) × (Auxiliary n → Bool),
          auxPins Z.2 * f (Sum.elim Z.1 Z.2 ∘ owner) := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow _ _ _)
      intro X
      congr 1
      apply congrArg f
      funext i
      cases h : owner i <;>
        simp only [Function.comp_apply, h, Sum.elim_inl, Sum.elim_inr,
          Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.sumArrowEquivProdArrow_apply_snd]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [auxPins_indicator, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq']
      rfl

/-- Row-by-row shift evaluation: potential pair rows remain NAND or one, and
the physical four-port copy gadget becomes the logical equality. -/
theorem rowExtensions_product (enabled : Pair n → Bool) (x : Occurrence n → Bool) :
    (∏ r : Row n, extension (rowTable (K := K) enabled r) (fun j =>
      -bit (pinnedColumns x (owner ⟨r,j⟩)))) =
    logicalPairs enabled x * logicalLinks x := by
  let f : Row n → K := fun r =>
    extension (rowTable enabled r) (fun j => -bit (pinnedColumns x (owner ⟨r,j⟩)))
  change (∏ r, f r) = _
  rw [Fintype.prod_sum_type f, logicalPairs, logicalLinks]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro p hp
    exact switch_extension (enabled p) (x ∘ pairOccurrence p)
  · apply Finset.prod_congr rfl
    intro l hl
    change extension (copyTable (K := K)) (fun j =>
      -bit (pinnedColumns x (owner ⟨.inr l,j⟩))) = _
    have localRead :
        (fun j : Bool × Bool => (-bit (pinnedColumns x (owner ⟨.inr l,j⟩)) : K)) =
          (fun j => if j.2 then -1 else -bit (x (stepOccurrence l j.1))) := by
      funext j
      rcases j with ⟨b,c⟩
      cases c <;> simp [owner, pinnedColumns, bit]
    rw [localRead]
    exact shiftedCopy (x ∘ stepOccurrence l)

/-- The desired physical host, with independent port assignments and
all-ones/zero-pinned dummy terminals at the even/odd wires. -/
noncomputable def shiftedHost (enabled : Pair n → Bool) (earlier : Wire n → Option (Wire n)) : K :=
  pairedRegister (rowProduct (rowTable enabled)) columnTable earlier

theorem shiftedHost_eq (hn : 0 < n) (enabled : Pair n → Bool)
    (earlier : Wire n → Option (Wire n)) :
    shiftedHost (K := K) enabled earlier = (count enabled : K) := by
  rw [shiftedHost, pairedRegister_collapse, column_elimination hn]
  rw [← logical_count (K := K) enabled]
  apply Finset.sum_congr rfl
  intro x hx
  rw [extension_rowProduct]
  exact rowExtensions_product enabled x

/-- At zero, each actual old row sees the physical pinned zero columns,
where both the disabled/enabled pair and the fixed copy table equal one. -/
noncomputable def hostOrigin (enabled : Pair n → Bool) : K := by
  classical
  exact ∑ x : Wire n → Bool, ∑ t : Wire n → Bool,
    columnTable x * (pinsZero t * rowProduct (rowTable enabled) t)

theorem hostOrigin_eq (hn : 0 < n) (enabled : Pair n → Bool) :
    hostOrigin (K := K) enabled = (2 : K)^((n+1)^2) := by
  classical
  rw [hostOrigin]
  have hrow : (rowProduct (rowTable enabled) (fun _ => false) : K) = 1 := by
    unfold rowProduct
    apply Finset.prod_eq_one
    intro r hr
    cases r with
    | inl p => cases h : enabled p <;> simp [rowTable, switchTable, nandTable, bit, h]
    | inr l => simp [rowTable, copyTable]
  have hpin (x t : Wire n → Bool) :
      columnTable (K := K) x * (pinsZero t * rowProduct (rowTable enabled) t) =
      if t = (fun _ => false) then columnTable x else 0 := by
    by_cases ht : t = (fun _ => false)
    · simp [ht, pinsZero_eq, hrow]
    · simp [ht, pinsZero_eq]
  simp_rw [hpin, Fintype.sum_ite_eq']
  have hsum := column_elimination (K := K) hn (fun _ => 1)
  simp only [mul_one] at hsum
  rw [hsum]
  simp [Occurrence, pow_two]

end Physical

/-- Certificate for the fixed physical layout. It contains no input graph
switches. The caller may instantiate it with a checked source packing. -/
structure Placement (n : ℕ) (P : Type*) where
  packet : Wire n × Bool → P
  position : Wire n × Bool → ℤ
  earlier : Wire n → Option (Wire n)
  predecessor : Wire n × Bool → Option (Wire n × Bool)
  exact_predecessor : ∀ x y, predecessor x = some y ↔
    packet x = packet y ∧ position y + 1 = position x
  odd : ∀ i, predecessor (i,true) = some (i,false)
  even : ∀ i, predecessor (i,false) = (earlier i).map (fun j => (j,true))

noncomputable def fixedMeshSlot {K : Type*} [CommRing K] {P : Type*} [DecidableEq P] {n : ℕ}
    (L : ℕ) (layout : Placement n P) (enabled : Pair n → Bool) : K :=
  pairedMeshRegister (rowProduct (rowTable enabled)) columnTable L layout.packet layout.position

/-- Exact A2 acquisition at the one named completed shifted Cauchy register.
The input changes one Boolean table entry per potential edge, never the host. -/
theorem fixedMeshSlot_decode {P : Type*} [DecidableEq P] {n : ℕ} (hn : 0 < n)
    (L : ℕ) (hL : 0 < L) (layout : Placement n P) (enabled : Pair n → Bool)
    {p : ℕ} (precision : n + 1 < p) :
    (fixedMeshSlot (K := ZMod (2^p)) L layout enabled).val = count enabled := by
  rw [fixedMeshSlot, pairedMeshRegister_eq _ _ L hL layout.packet layout.position
    layout.earlier layout.predecessor layout.exact_predecessor layout.odd layout.even]
  change (shiftedHost (K := ZMod (2^p)) enabled layout.earlier).val = count enabled
  rw [shiftedHost_eq hn, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt ((count_le enabled).trans_lt (Nat.pow_lt_pow_right (by decide) precision))


section Toggle

variable {n : ℕ}

def setSwitch (enabled : Pair n → Bool) (p : Pair n) (b : Bool) (q : Pair n) : Bool :=
  if q = p then b else enabled q

def bothEnds (p : Pair n) (x : Vertex n → Bool) : Prop :=
  x p.1.1 = true ∧ x p.1.2 = true

theorem switch_on_iff (enabled : Pair n → Bool) (p : Pair n) (x : Vertex n → Bool) :
    IsIndependent (setSwitch enabled p true) x ↔
      IsIndependent (setSwitch enabled p false) x ∧ ¬ bothEnds p x := by
  constructor
  · intro h
    refine ⟨?_, h p (by simp [setSwitch])⟩
    intro q em
    by_cases qeq : q = p
    · subst q
      simp [setSwitch] at em
    · apply h q
      simpa [setSwitch, qeq] using em
  · rintro ⟨h, hp⟩ q eq
    by_cases qeq : q = p
    · subst q
      exact hp
    · apply h q
      simpa [setSwitch, qeq] using eq

/-- The exact change in the count on one toggle, with all other switches
held fixed: precisely the formerly legal sets containing both endpoints. -/
noncomputable def removedCount (enabled : Pair n → Bool) (p : Pair n) : ℕ := by
  classical
  exact (((Finset.univ : Finset (Vertex n → Bool)).filter
    (IsIndependent (setSwitch enabled p false))).filter (bothEnds p)).card

theorem switch_count_exact (enabled : Pair n → Bool) (p : Pair n) :
    count (setSwitch enabled p false) =
      count (setSwitch enabled p true) + removedCount enabled p := by
  classical
  let off := (Finset.univ : Finset (Vertex n → Bool)).filter (IsIndependent (setSwitch enabled p false))
  have subset_eq : off.filter (fun x => ¬ bothEnds p x) =
      (Finset.univ : Finset (Vertex n → Bool)).filter (IsIndependent (setSwitch enabled p true)) := by
    ext x
    simp only [off, Finset.mem_filter, Finset.mem_univ, true_and, switch_on_iff]
  have split := Finset.filter_card_add_filter_neg_card_eq_card (s := off) (bothEnds p)
  rw [subset_eq] at split
  rw [add_comm]
  exact split.symm

theorem removedCount_pos (enabled : Pair n → Bool) (p : Pair n) : 0 < removedCount enabled p := by
  classical
  let x : Vertex n → Bool := fun v => decide (v = p.1.1 ∨ v = p.1.2)
  have independent : IsIndependent (setSwitch enabled p false) x := by
    intro q active clash
    have h₁ : q.1.1 = p.1.1 ∨ q.1.1 = p.1.2 := of_decide_eq_true clash.1
    have h₂ : q.1.2 = p.1.1 ∨ q.1.2 = p.1.2 := of_decide_eq_true clash.2
    have eql : q = p := by
      have gt := q.2
      rcases h₁ with a | a <;> rcases h₂ with b | b
      · rw [a,b] at gt
        exact (lt_irrefl _ gt).elim
      · exact Subtype.ext (Prod.ext a b)
      · rw [a,b] at gt
        exact (lt_asymm p.2 gt).elim
      · rw [a,b] at gt
        exact (lt_irrefl _ gt).elim
    simp [setSwitch, eql] at active
  have both : bothEnds p x := by simp [bothEnds, x]
  unfold removedCount
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, independent⟩, both⟩⟩

theorem switch_count_strict (enabled : Pair n → Bool) (p : Pair n) :
    count (setSwitch enabled p true) < count (setSwitch enabled p false) := by
  have hp := removedCount_pos enabled p
  rw [switch_count_exact]
  omega

/-- The exact single-table toggle response is visible in the actual high-
precision one-register acquisition, not merely the abstract count. -/
theorem fixedMeshSlot_switch_exact {P : Type*} [DecidableEq P] (hn : 0 < n)
    (L : ℕ) (hL : 0 < L) (layout : Placement n P) (enabled : Pair n → Bool) (e : Pair n)
    {p : ℕ} (precision : n+1 < p) :
    (fixedMeshSlot (K := ZMod (2^p)) L layout (setSwitch enabled e false)).val =
      (fixedMeshSlot (K := ZMod (2^p)) L layout (setSwitch enabled e true)).val + removedCount enabled e := by
  rw [fixedMeshSlot_decode hn L hL layout _ precision, fixedMeshSlot_decode hn L hL layout _ precision]
  exact switch_count_exact enabled e

end Toggle


#print axioms shiftedCopy
#print axioms coherent_iff
#print axioms logical_count
#print axioms physical_wire_bound
#print axioms fixed_column_degree
#print axioms fixed_row_degree
#print axioms shiftedHost_eq
#print axioms hostOrigin_eq
#print axioms fixedMeshSlot_decode
#print axioms fixedMeshSlot_switch_exact
#print axioms switch_count_strict

end FixedHostAcquisition
