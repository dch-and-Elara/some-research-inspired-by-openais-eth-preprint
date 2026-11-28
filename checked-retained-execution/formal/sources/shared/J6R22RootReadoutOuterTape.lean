
import J6R22RootReadoutTerms
import J6R22RootReadoutNativeFactor

/-! Acquisition is separate. After the certified sample and coordinate
tape is in hand, every Lagrange factor, pair sum, guard subtraction, and
final restoring division is paid here. -/
namespace J6R22RootReadout
open scoped Polynomial BigOperators Classical
open Polynomial J6Mesh J6NativeHeightMesh J9R19CompiledBits
open A1R10 A1R12 AOracleMachineTime
set_option maxHeartbeats 17000000
set_option maxRecDepth 1500
set_option linter.unusedSectionVars false

def outPrepFee (p m : ℕ) :=
  (m+1)*(outerTermFee p m+12*p+12)+12

def prepareTerms {p : ℕ} (hp : 0<p) (m : ℕ) (xs : List (CoordinateWord p)) :
    Meter (List (FractionWord p)) :=
  let slots := List.ofFn (termWord hp xs : Fin (m+1)→_)
  ⟨slots.map Meter.result,(slots.map Meter.steps).sum+(m+1)*(12*p+12)+12⟩

private theorem map_rel {I X Y : Type*} (R : X→Y→Prop) (f : I→X) (g : I→Y)
    (xs : List I) (h : ∀ i,R (f i) (g i)) :
    List.Forall₂ R (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons i xs ih => exact .cons (h i) ih

private theorem sum_bounded (xs : List ℕ) (C : ℕ) (h : ∀ n∈xs,n≤C) :
    xs.sum≤xs.length*C := by
  induction xs with
  | nil => simp
  | cons n xs ih =>
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,one_mul]
    have H := ih (fun v hv=>h v (List.mem_cons_of_mem _ hv))
    have hN := h n List.mem_cons_self
    omega

theorem prepare_terms_exact {p m : ℕ} (hp : 0<p)
    (xs : List (CoordinateWord p)) (len : xs.length=m+1) (n d A : Fin (m+1)→ℤ)
    (chart : ∀ j : Fin (m+1), xs[j.val]'(by rw [len]; exact j.isLt) |>.realizes (n j) (d j) (A j)) :
    List.Forall₂ FractionWord.matches (prepareTerms hp m xs).result (outerTermTape m n d A) ∧
    (prepareTerms hp m xs).steps≤outPrepFee p m := by
  have t (i : Fin (m+1)) := term_word_exact hp xs len n d A chart i
  constructor
  · change List.Forall₂ FractionWord.matches ((List.ofFn (termWord hp xs : Fin (m+1)→_)).map Meter.result) _
    rw [List.map_ofFn,outerTermTape,List.ofFn_eq_map,List.ofFn_eq_map]
    exact map_rel FractionWord.matches _ _ _ (fun i=>(t i).1)
  · let slots := List.ofFn (termWord hp xs : Fin (m+1)→_)
    have C := sum_bounded (slots.map Meter.steps) (outerTermFee p m) (by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hj
      rw [←hi]
      exact (t i).2)
    simp only [List.length_map,List.length_ofFn,slots] at C
    change (slots.map Meter.steps).sum+(m+1)*(12*p+12)+12≤_
    calc
      _ ≤ (m+1)*outerTermFee p m+(m+1)*(12*p+12)+12 :=
        Nat.add_le_add_right (Nat.add_le_add_right C _) _
      _ = _ := by unfold outPrepFee; ring

theorem prepared_length {p m : ℕ} (hp : 0<p) (xs : List (CoordinateWord p)) :
    (prepareTerms hp m xs).result.length=m+1 := by
  simp [prepareTerms]

def outerWordCount {p : ℕ} (hp : 0<p) (m : ℕ) (xs : List (CoordinateWord p)) :
    Meter (Word p) :=
  let a := prepareTerms hp m xs
  let b := finishWords hp a.result
  ⟨b.result,a.steps+b.steps+2⟩

def printedOuterFee (p m : ℕ) :=
  outPrepFee p m+(4*p+10+(m+1)*commonWordFee p+dropGuardFee p)+2

theorem outer_word_count_exact {p m b hA : ℕ} (hp : 0<p)
    (xs : List (CoordinateWord p)) (len : xs.length=m+1) (n d A : Fin (m+1)→ℤ)
    (chart : ∀ j : Fin (m+1), xs[j.val]'(by rw [len]; exact j.isLt) |>.realizes (n j) (d j) (A j))
    (hn : ∀ j,Fits b (n j)) (hd : ∀ j,Fits b (d j)) (hs : ∀ j,Fits hA (A j))
    (nonzero : ∀ j,d j≠0) (distinct : Function.Injective (fun j=>(n j:ℚ)/d j))
    (k : ℕ) (truth : (outerAtOne m n d A).value-1=(k:ℚ))
    (capacity : (baseTermWidth m b hA+1)*(m+1)+3≤p) :
    bitsValue (outerWordCount hp m xs).result.val=k ∧
    (outerWordCount hp m xs).steps≤printedOuterFee p m := by
  have C := prepare_terms_exact hp xs len n d A chart
  have fit : ∀ x∈outerTermTape m n d A,x.fits (baseTermWidth m b hA) := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact term_at_one_fits m b hA n d A i hn hd hs
  have good : ∀ x∈outerTermTape m n d A,x.good := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact term_at_one_good m n d A i nonzero distinct
  have Q := finish_words_exact hp _ _ k C.1 good fit
    (by simpa only [outerTermTape,List.length_ofFn] using capacity) truth
  refine ⟨Q.1,?_⟩
  change (prepareTerms hp m xs).steps+(finishWords hp (prepareTerms hp m xs).result).steps+2≤_
  have e := Q.2
  rw [prepared_length hp xs] at e
  exact Nat.add_le_add_right (Nat.add_le_add C.2 e) _

theorem native_odd_mesh_word_count {p m h : ℕ} (hp : 0<p)
    (xs : List (CoordinateWord p)) (len : xs.length=m+1) (A : Fin (m+1)→ℤ)
    (chart : ∀ j : Fin (m+1), xs[j.val]'(by rw [len]; exact j.isLt) |>.realizes
      (sampleNum m j) (sampleDen m j) (A j))
    (hs : ∀ j,Fits h (A j)) (k : ℕ)
    (truth : (outerAtOne m (sampleNum m) (sampleDen m) A).value-1=(k:ℚ))
    (capacity : (baseTermWidth m (outerMeshWidth m) h+1)*(m+1)+3≤p) :
    bitsValue (outerWordCount hp m xs).result.val=k ∧
    (outerWordCount hp m xs).steps≤printedOuterFee p m :=
  outer_word_count_exact hp xs len _ _ A chart (fun j=>(source_mesh_fits m j).1)
    (fun j=>(source_mesh_fits m j).2) hs (fun j=>(mesh_bounds m j).1.ne') (source_mesh_injective m) k truth capacity

#print axioms prepare_terms_exact
#print axioms prepared_length
#print axioms outer_word_count_exact
#print axioms native_odd_mesh_word_count
end J6R22RootReadout
