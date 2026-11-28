import J6R22ActiveSite

/-! Settlement of recursive receipts by occurrence, not by equality of Call
records. These are exact fee differences between the *same raw computation*
fed the same words, with or without the previously incurred child charge. -/
namespace J6R24MeteredRecursion
open A1R10 A1R12 AOracleMachineTime J6R22Active

def bare {A : Type*} (x : Meter A) : Meter A := ⟨x.result,0⟩

structure Delta {A : Type*} (paid base : Meter A) (extra : ℕ) : Prop where
  value : paid.result=base.result
  fee : paid.steps=base.steps+extra

theorem Delta.bare {A : Type*} (x : Meter A) : Delta x (bare x) x.steps :=
  ⟨rfl,by change x.steps=0+x.steps; exact (Nat.zero_add _).symm⟩

theorem Delta.refl {A : Type*} (x : Meter A) : Delta x x 0 := ⟨rfl,by simp⟩

theorem Delta.pad {A : Type*} {x y : Meter A} {j : ℕ} (h : Delta x y j) (k : ℕ) :
    Delta (padCost x k) (padCost y k) j :=
  ⟨h.value,by dsimp [padCost]; have := h.fee; omega⟩

section UV
variable {p ell : ℕ} {fw : List (Word p)} (hp : 0<p)
variable {x y u v : Meter (UVBlock fw ell)} {j k : ℕ}

theorem add_delta (h : Delta x u j) (h' : Delta y v k) :
    Delta (addM hp x y) (addM hp u v) (j+k) := by
  refine ⟨?_,?_⟩
  · simp only [addM,h.value,h'.value]
  · simp only [addM,h.value,h'.value,h.fee,h'.fee]
    omega

theorem mul_delta (h : Delta x u j) (h' : Delta y v k) :
    Delta (mulM hp x y) (mulM hp u v) (j+k) := by
  refine ⟨?_,?_⟩
  · simp only [mulM,h.value,h'.value]
  · simp only [mulM,h.value,h'.value,h.fee,h'.fee]
    omega

theorem sum_delta {A : Type*} (g h : A→Meter (UVBlock fw ell)) (f : A→ℕ)
    (as : List A) (d : ∀ a∈as,Delta (g a) (h a) (f a)) :
    Delta (sumM hp g as) (sumM hp h as) (as.map f).sum := by
  induction as with
  | nil => exact Delta.refl _
  | cons a as ih =>
    simpa only [sumM,List.map_cons,List.sum_cons] using
      add_delta hp (d a List.mem_cons_self) (ih (fun z hz=>d z (List.mem_cons_of_mem _ hz)))

theorem product_delta {A : Type*} (he : 0<fw.length) (hv : 0<ell)
    (g h : A→Meter (UVBlock fw ell)) (f : A→ℕ) (as : List A)
    (d : ∀ a∈as,Delta (g a) (h a) (f a)) :
    Delta (foldM hp he hv g as) (foldM hp he hv h as) (as.map f).sum := by
  induction as with
  | nil => exact Delta.refl _
  | cons a as ih =>
    simpa only [foldM,List.map_cons,List.sum_cons] using
      mul_delta hp (d a List.mem_cons_self) (ih (fun z hz=>d z (List.mem_cons_of_mem _ hz)))

theorem probe_delta {A : Type*} {G : ℕ} (he : 0<fw.length) (hv : 0<ell)
    (xs : List A) (rd : A→Fin G→Meter (UVBlock fw ell)) :
    Delta (groupedProbe hp he hv xs rd)
      (groupedProbe hp he hv xs (fun a j=>bare (rd a j))) (probeEntryBill xs rd) := by
  apply sum_delta hp
  intro a _
  exact product_delta hp he hv _ _ _ _ (fun j _=>Delta.bare (rd a j))

theorem jet_sum_delta {A : Type*} {k : ℕ} (he : 0<fw.length)
    (g h : A→Meter (JetTape fw ell k)) (f : A→ℕ) (as : List A)
    (d : ∀ a∈as,Delta (g a) (h a) (f a)) :
    Delta (paidJetSum hp he g as) (paidJetSum hp he h as) (as.map f).sum := by
  induction as with
  | nil => exact Delta.refl _
  | cons a as ih =>
    have p := d a List.mem_cons_self
    have q := ih (fun z hz=>d z (List.mem_cons_of_mem _ hz))
    refine ⟨?_,?_⟩
    · simp only [paidJetSum,p.value,q.value]
    · simp only [paidJetSum,p.value,q.value,p.fee,q.fee,List.map_cons,List.sum_cons]
      omega

theorem prefix_delta (he : 0<fw.length) (hv : 0<ell) {k n : ℕ} (hk : 0<k)
    (node s t : Fin n→Meter (UVBlock fw ell)) (f : Fin n→ℕ)
    (d : ∀ a,Delta (s a) (t a) (f a)) :
    Delta (interpPrefix hp he hv hk node s) (interpPrefix hp he hv hk node t)
      ((probeOrder n).map f).sum := by
  have ht (i : Fin n) : Delta (interpTerm hp he hv hk node s i)
      (interpTerm hp he hv hk node t i) (f i) := by
    have d0 := d i
    refine ⟨?_,?_⟩
    · simp only [interpTerm,d0.value]
    · simp only [interpTerm,d0.value,d0.fee]
      omega
  have h := jet_sum_delta hp he _ _ f (probeOrder n) (fun i _=>ht i)
  refine ⟨?_,?_⟩
  · simp only [interpPrefix,h.value]
  · simp only [interpPrefix,h.fee]
    omega

theorem full_delta (he : 0<fw.length) (hv : 0<ell) {k n : ℕ} (hk : 0<k)
    (node s t : Fin n→Meter (UVBlock fw ell)) (f : Fin n→ℕ)
    (norm : Meter (JetTape fw ell k)) (d : ∀ a,Delta (s a) (t a) (f a)) :
    Delta (fullCenterM hp he hv hk node s norm) (fullCenterM hp he hv hk node t norm)
      ((probeOrder n).map f).sum := by
  have h := prefix_delta hp he hv hk node s t f d
  refine ⟨?_,?_⟩
  · simp only [fullCenterM,h.value]
  · simp only [fullCenterM,h.value,h.fee]
    omega
end UV

def SiteTape.bareChildren {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode) : SiteTape p ell k n Mode :=
  { I with child := fun z β g=>bare (I.child z β g) }

theorem site_delta {p ell k n : ℕ} {Mode : Type*} (I : SiteTape p ell k n Mode)
    (a : ℕ) (t : ℤ) :
    Delta (I.run a t) ((SiteTape.bareChildren I).run a t) I.childBill := by
  exact full_delta I.hp I.nonempty I.he I.hk I.nodeM I.groupedM (SiteTape.bareChildren I).groupedM
    (fun z=>probeEntryBill I.modes (I.child z)) (I.normM a t)
    (fun z=>probe_delta I.hp I.nonempty I.he I.modes (I.child z))

#print axioms probe_delta
#print axioms full_delta
#print axioms site_delta
end J6R24MeteredRecursion

