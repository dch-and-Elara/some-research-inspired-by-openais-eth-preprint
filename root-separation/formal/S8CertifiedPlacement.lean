import S8PinConflicts

namespace S8

set_option maxSynthPendingDepth 16
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

open scoped BigOperators
open SourceDensity GraphCutMoments

variable {V G J I A : Type*}
  [Fintype V] [DecidableEq V] [Nonempty V] [Fintype G] [DecidableEq G]
  [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype A] [DecidableEq A] [Nonempty A]

def pinClass (E : Finset (V × V)) (f : V → G) : Clause E → Option G :=
  fun c => c.elim (some ∘ f) (fun _ => none)

def oldPinClass (E : Finset (V × V)) (f : V → G) : OldVertex E → Option G :=
  fun c => c.elim (fun _ => none) (pinClass E f)

omit [Fintype V] [Nonempty V] [Fintype G] [DecidableEq G] in
theorem port_is_pin (E : Finset (V × V)) (f : V → G) (v : MainClonedCNF.Port E) (g : G)
    (h : pinClass E f (portClause E v) = some g) :
    ∃ x, v = MainClonedCNF.pinPort E x ∧ f x = g := by
  rcases v with (v | (⟨e,b⟩ | ⟨v,i,b⟩)) <;>
    simp_all [pinClass, portClause, MainClonedCNF.pinPort]

omit [Fintype V] [Nonempty V] [Fintype G] [DecidableEq G] in
theorem wire_is_pin (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (f : V → G)
    (w : Wire E) (g : G) (h : oldPinClass E f (wireOld E reg w) = some g) :
    ∃ x, w = pinWire E x ∧ f x = g := by
  obtain ⟨p,b⟩ := w
  cases b
  · simp [wireOld, oldPinClass] at h
  · have hh : pinClass E f (portClause E p) = some g := by
      simpa [wireOld, oldPinClass] using h
    obtain ⟨x,rfl,hx⟩ := port_is_pin E f p g hh
    exact ⟨x,rfl,hx⟩

local instance portEq (E : Finset (V × V)) : DecidableEq (MainClonedCNF.Port E) :=
  letI : DecidableEq (E × Bool) := inferInstance
  letI : DecidableEq (V × Fin 4 × Bool) := inferInstance
  letI : DecidableEq ((E × Bool) ⊕ (V × Fin 4 × Bool)) := inferInstance
  inferInstanceAs (DecidableEq (V ⊕ ((E × Bool) ⊕ (V × Fin 4 × Bool))))

local instance wireEq (E : Finset (V × V)) : DecidableEq (Wire E) :=
  inferInstanceAs (DecidableEq (MainClonedCNF.Port E × Bool))

local instance oldEq (E : Finset (V × V)) : DecidableEq (OldVertex E) :=
  letI : DecidableEq (Clause E) := inferInstance
  inferInstanceAs (DecidableEq ((V × Fin 4) ⊕ Clause E))

abbrev MainPrimitive (E : Finset (V × V)) (G I : Type*) :=
  Primitive (V × Fin 4) (Clause E) Empty G I

abbrev DPrimitive (E : Finset (V × V)) (G I : Type*) :=
  Primitive (OldVertex E) (MainClonedCNF.Port E) G Empty I

noncomputable def sampleMain (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (t : I)
    (f : V → G) (ω : MainPrimitive E G I → A) :=
  words (portClone E reg) (portClause E) (fun _ => (none : Option Empty)) (pinClass E f) t ω

noncomputable def sampleD (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (t : I)
    (f : V → G) (ω : DPrimitive E G I → A) :=
  words (wireOld E reg) (fun w : Wire E => w.1) (oldPinClass E f)
    (fun _ => (none : Option Empty)) t ω

@[simp] theorem sampleMain_pin (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (t : I) (f : V → G) (ω : MainPrimitive E G I → A) (v : V) :
    (sampleMain E reg t f ω (MainClonedCNF.pinPort E v)).2 t =
      ω (t, .inr (.inr (f v))) := by
  simp [sampleMain, words, site, key, pinClass, portClause, MainClonedCNF.pinPort]

@[simp] theorem sampleD_pin (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (t : I) (f : V → G) (ω : DPrimitive E G I → A) (v : V) :
    (sampleD E reg t f ω (pinWire E v)).1 t = ω (t, .inl (.inr (f v))) := by
  simp [sampleD, words, site, key, oldPinClass, pinClass, portClause, pinWire, wireOld,
    MainClonedCNF.pinPort]

theorem main_collision_moment (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (t : I)
    (owner : V ≃ G × Fin 3) :
    (∑ ω : MainPrimitive E G I → A, ProductVariance.uniformWeight (MainPrimitive E G I → A) *
      collision (sampleMain E reg t (fun v => (owner v).1) ω)) ≤
      4 * Fintype.card (MainClonedCNF.Port E) + 2 * Fintype.card V := by
  let extra := pinNeighbors (MainClonedCNF.pinPort E) owner
  let bad := conflictPairs (portClone E reg) (portClause E) extra
  have hm := mean_words (A := A)
    (portClone E reg) (portClause E) (fun _ => (none : Option Empty))
    (pinClass E (fun v => (owner v).1)) t bad
  have good := separate_sites (portClone E reg) (portClause E) (fun _ => (none : Option Empty))
    (pinClass E (fun v => (owner v).1)) extra t (by simp) (by
      intro e f g he hf hn
      obtain ⟨v,rfl,hv⟩ := port_is_pin E _ e g he
      obtain ⟨w,rfl,hw⟩ := port_is_pin E _ f g hf
      exact pinNeighbors_mem _ _ v w (hv.trans hw.symm) (fun h => hn (by rw [h])))
  have hb := conflict_count (portClone E reg) (portClause E) extra 3 2
    (cloneDegree E reg) (clauseDegree E)
  change bad.card ≤ _ at hb
  simp only [extra, pinNeighbors_sum, Fintype.card_fin] at hb
  have hn : bad.card ≤ 4 * Fintype.card (MainClonedCNF.Port E) + 2 * Fintype.card V := by omega
  exact (hm good).trans (by push_cast at ⊢; exact_mod_cast hn)

theorem appendix_collision_moment (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (t : I)
    (owner : V ≃ G × Bool) :
    (∑ ω : DPrimitive E G I → A, ProductVariance.uniformWeight (DPrimitive E G I → A) *
      collision (sampleD E reg t (fun v => (owner v).1) ω)) ≤
      4 * Fintype.card (Wire E) + Fintype.card V := by
  let extra := pinNeighbors (pinWire E) owner
  let bad := conflictPairs (wireOld E reg) (fun w : Wire E => w.1) extra
  have hm := mean_words (A := A)
    (wireOld E reg) (fun w : Wire E => w.1) (oldPinClass E (fun v => (owner v).1))
    (fun _ => (none : Option Empty)) t bad
  have good := separate_sites (wireOld E reg) (fun w : Wire E => w.1)
    (oldPinClass E (fun v => (owner v).1)) (fun _ => (none : Option Empty)) extra t (by
      intro e f g he hf hn
      obtain ⟨v,rfl,hv⟩ := wire_is_pin E reg _ e g he
      obtain ⟨w,rfl,hw⟩ := wire_is_pin E reg _ f g hf
      exact pinNeighbors_mem _ _ v w (hv.trans hw.symm) (fun h => hn (by rw [h]))) (by simp)
  have hb := conflict_count (wireOld E reg) (fun w : Wire E => w.1) extra 3 2
    (wireOldDegree E reg) (subdivDegree E)
  change bad.card ≤ _ at hb
  simp only [extra, pinNeighbors_sum, Fintype.card_bool] at hb
  have hn : bad.card ≤ 4 * Fintype.card (Wire E) + Fintype.card V := by omega
  exact (hm good).trans (by exact_mod_cast hn)

section Feasible

theorem exists_main_placement (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (t : I)
    (owner : V ≃ G × Fin 3)
    (incFeasible : 10 * Fintype.card ((I → A) × (I → A))^2 ≤
      Fintype.card (MainClonedCNF.Port E))
    (groupFeasible : 2 * Fintype.card I * Fintype.card A ^ 2 ≤ Fintype.card (V × Fin 4)) :
    ∃ ω : MainPrimitive E G I → A,
      (∀ c, (fiberCount (sampleMain E reg t (fun v => (owner v).1) ω) c : ℚ) ≤
        2 * Fintype.card (MainClonedCNF.Port E) / Fintype.card ((I → A) × (I → A))) ∧
      (∀ i a, (fiberCount (mainVariable ω i) a : ℚ) ≤
        2 * Fintype.card (V × Fin 4) / Fintype.card A) := by
  let M := (Fintype.card (MainClonedCNF.Port E) : ℚ)
  let n := (Fintype.card (V × Fin 4) : ℚ)
  let Q := (Fintype.card I : ℚ)
  have hM : 0 < M := by dsimp [M]; rw [MainClonedCNF.port_card E reg]; positivity
  have hm : 2 * (Fintype.card V : ℚ) ≤ M := by
    have h := MainClonedCNF.port_card E reg
    dsimp [M]
    exact_mod_cast (show 2 * Fintype.card V ≤ Fintype.card (MainClonedCNF.Port E) by omega)
  have hinc := main_collision_moment (A := A) E reg t owner
  have hin : 4 * (Fintype.card (MainClonedCNF.Port E) : ℚ) + 2 * Fintype.card V ≤ 5*M := by
    change 4*M + 2*Fintype.card V ≤ 5*M
    linarith only [hm]
  refine main_certificates_of_moments _ uniform_mass
    (fun _ => by unfold ProductVariance.uniformWeight; positivity)
    _ (fun ω i v => mainVariable ω i v) (5*M) (Q*n) (by positivity)
    (by dsimp [Q,n]; positivity) (hinc.trans hin) ?_ ?_ ?_
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum fun i _ => uniform_variable_moment (A := A) (G := G) (Y := Clause E) i).trans_eq (by
      simp [Q,n, nsmul_eq_mul])
  · have hi : 10 * (Fintype.card ((I → A) × (I → A)) : ℚ)^2 ≤ M := by
      dsimp [M]; exact_mod_cast incFeasible
    nlinarith only [mul_le_mul_of_nonneg_right hi hM.le]
  · have hi : 2 * Q * (Fintype.card A : ℚ)^2 ≤ n := by dsimp [Q,n]; exact_mod_cast groupFeasible
    have hn : 0 ≤ n := by dsimp [n]; positivity
    nlinarith only [mul_le_mul_of_nonneg_right hi hn]

theorem exists_appendix_placement (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (t : I)
    (owner : V ≃ G × Bool) (Δ : ℚ) (hΔ : 3 ≤ Δ)
    (feasible : 2 * (Fintype.card ((I → A) × (I → A)) : ℚ)^2 * Δ ≤
      Fintype.card (Wire E)) :
    ∃ ω : DPrimitive E G I → A,
      CollisionCertificate (sampleD E reg t (fun v => (owner v).1) ω) Δ := by
  refine appendixD_certificate_of_moment _ uniform_mass
    (fun _ => by unfold ProductVariance.uniformWeight; positivity) _ Δ ?_ feasible
  have h := appendix_collision_moment (A := A) E reg t owner
  have hn : (Fintype.card V : ℚ) ≤ Fintype.card (Wire E) := by
    have hc := wire_card E reg
    exact_mod_cast (show Fintype.card V ≤ Fintype.card (Wire E) by omega)
  have hp : 0 ≤ 2 * (Fintype.card (Wire E) : ℚ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hΔ hp
  exact h.trans (by nlinarith only [hn, hh])

end Feasible

#print axioms sampleMain_pin
#print axioms sampleD_pin
#print axioms main_collision_moment
#print axioms appendix_collision_moment
#print axioms exists_main_placement
#print axioms exists_appendix_placement

end S8

