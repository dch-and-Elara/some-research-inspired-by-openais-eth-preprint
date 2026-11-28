import V8NativeMessageC3NativeAssemblyN2MainClone

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5800000

/-! The actual N2 contribution gate, applied to measurement rows whose
nonnegative rows cover their columns. The concrete weight-zero source
row theorem discharges this hypothesis for the printed MAIN layout. -/
namespace V8NativeMessage.N6.MainFiber
open V8NativeMessage.C3.NativeAssembly.MainScan
open scoped BigOperators Classical

noncomputable section

variable {V G : Type*} [Fintype V]

def zeroWord (L : Frame V G) (g : G) : Word L g := fun _=>false

def oneWord (L : Frame V G) (g : G) : Word L g := fun _=>true

def zeroTarget (L : Frame V G) : Prop := ∀ g j,L.y g j=0

def oneTarget (L : Frame V G) : Prop := ∀ g j,L.y g j=V8NativeMessage.C3.NativeAssembly.MainScan.measure L g (oneWord L g) j

def positiveCover (L : Frame V G) : Prop :=
  ∀ g (v : {v : V // L.group v=g}),∃ j : Fin (L.rows g),
    (∀ w,0≤L.C g j w) ∧ 0<L.C g j v

def touches (L : Frame V G) (g : G) : Prop :=
  ∃ v : {v : V // L.group v=g},v.val∈L.E

theorem measure_zero_word (L : Frame V G) (g : G) (j : Fin (L.rows g)) :
    V8NativeMessage.C3.NativeAssembly.MainScan.measure L g (zeroWord L g) j=0 := by simp [V8NativeMessage.C3.NativeAssembly.MainScan.measure,zeroWord]

theorem measure_complement (L : Frame V G) (g : G) (x : Word L g) (j : Fin (L.rows g)) :
    V8NativeMessage.C3.NativeAssembly.MainScan.measure L g (fun v=> !x v) j=V8NativeMessage.C3.NativeAssembly.MainScan.measure L g (oneWord L g) j-V8NativeMessage.C3.NativeAssembly.MainScan.measure L g x j := by
  unfold V8NativeMessage.C3.NativeAssembly.MainScan.measure
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  cases hv : x v <;> simp [oneWord,hv]

theorem zero_unrestricted_iff (L : Frame V G) (hC : positiveCover L)
    (h0 : zeroTarget L) (g : G) (x : Word L g) :
    unrestricted L g x ↔ x=zeroWord L g := by
  constructor
  · intro hx
    funext v
    cases hv : x v with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨j,hNN,hPos⟩ := hC g v
      have hSum := (hx j).trans (h0 g j)
      have hBound : L.C g j v≤V8NativeMessage.C3.NativeAssembly.MainScan.measure L g x j := by
        unfold V8NativeMessage.C3.NativeAssembly.MainScan.measure
        simpa only [hv,if_true,mul_one] using
          (Finset.single_le_sum
            (f:=fun w : {w : V // L.group w=g}=>L.C g j w*(if x w then (1:ℤ) else 0))
            (fun w _=>mul_nonneg (hNN w) (by split <;> norm_num)) (Finset.mem_univ v))
      omega
  · rintro rfl j
    rw [measure_zero_word,h0]

theorem one_unrestricted_iff (L : Frame V G) (hC : positiveCover L)
    (h1 : oneTarget L) (g : G) (x : Word L g) :
    unrestricted L g x ↔ x=oneWord L g := by
  constructor
  · intro hx
    let Z : Frame V G := {L with y:=fun _ _=>0}
    have hC' : positiveCover Z := hC
    have hz : unrestricted Z g (fun v=> !x v) := by
      intro j
      change V8NativeMessage.C3.NativeAssembly.MainScan.measure L g (fun v=> !x v) j=0
      rw [measure_complement,hx j,h1 g j,sub_self]
    have hm : (fun v=> !x v)=zeroWord L g :=
      (zero_unrestricted_iff Z hC' (fun _ _=>rfl) g _).1 hz
    funext v
    have hv := congrFun hm v
    change (!x v)=false at hv
    cases e : x v <;> simp_all [oneWord]
  · rintro rfl j
    exact (h1 g j).symm

theorem zero_eligible_iff (L : Frame V G) (hC : positiveCover L)
    (h0 : zeroTarget L) (g : G) (x : Word L g) :
    eligible L g x ↔ x=zeroWord L g ∧ ¬touches L g := by
  unfold eligible
  rw [zero_unrestricted_iff L hC h0 g]
  constructor
  · rintro ⟨rfl,h⟩
    exact ⟨rfl,fun ⟨v,hv⟩=>Bool.noConfusion (h v hv)⟩
  · rintro ⟨rfl,h⟩
    exact ⟨rfl,fun v hv=>(h ⟨v,hv⟩).elim⟩

theorem one_eligible_iff (L : Frame V G) (hC : positiveCover L)
    (h1 : oneTarget L) (g : G) (x : Word L g) :
    eligible L g x ↔ x=oneWord L g := by
  unfold eligible
  rw [one_unrestricted_iff L hC h1 g]
  exact ⟨And.left,by rintro rfl;exact ⟨rfl,fun _ _=>rfl⟩⟩

theorem zero_feasible (L : Frame V G) (h0 : zeroTarget L) : feasible L := by
  apply (feasible_iff_unrestricted L).2
  exact fun g=>⟨zeroWord L g,fun j=>(measure_zero_word L g j).trans (h0 g j).symm⟩

theorem one_feasible (L : Frame V G) (h1 : oneTarget L) : feasible L :=
  (feasible_iff_unrestricted L).2 (fun g=>⟨oneWord L g,fun j=>(h1 g j).symm⟩)

theorem zero_rep_word (L : Frame V G) (hC : positiveCover L)
    (h0 : zeroTarget L) (h : feasible L) (g : G) :
    repWord L h g=zeroWord L g :=
  (zero_unrestricted_iff L hC h0 g _).1 (repWord_unrestricted L h g)

theorem zero_merge (L : Frame V G) (hC : positiveCover L)
    (h0 : zeroTarget L) (h : feasible L) (g : G) :
    merge L (repWord L h) g (zeroWord L g)=fun _=>false := by
  funext v
  unfold merge
  split
  · rfl
  · rw [zero_rep_word L hC h0]
    rfl

theorem touched_zero_filter (L : Frame V G) (hC : positiveCover L)
    (h0 : zeroTarget L) (g : G) (hE : touches L g) :
    (Finset.univ : Finset (Word L g)).filter (eligible L g)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact ((zero_eligible_iff L hC h0 g x).1 (Finset.mem_filter.mp hx).2).2 hE

theorem untouched_zero_filter (L : Frame V G) (hC : positiveCover L)
    (h0 : zeroTarget L) (g : G) (hE : ¬touches L g) :
    (Finset.univ : Finset (Word L g)).filter (eligible L g)={zeroWord L g} := by
  ext x
  simp [zero_eligible_iff L hC h0 g x,hE]

theorem one_filter (L : Frame V G) (hC : positiveCover L)
    (h1 : oneTarget L) (g : G) :
    (Finset.univ : Finset (Word L g)).filter (eligible L g)={oneWord L g} := by
  ext x
  simp [one_eligible_iff L hC h1 g x]

#print axioms measure_zero_word
#print axioms measure_complement
#print axioms zero_unrestricted_iff
#print axioms one_unrestricted_iff
#print axioms zero_eligible_iff
#print axioms one_eligible_iff
#print axioms zero_feasible
#print axioms one_feasible
#print axioms zero_rep_word
#print axioms zero_merge
#print axioms touched_zero_filter
#print axioms untouched_zero_filter
#print axioms one_filter

end
end V8NativeMessage.N6.MainFiber
