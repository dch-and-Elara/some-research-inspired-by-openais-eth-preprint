import P5AlwaysSatOriginalPorts
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The sign-independent occurrence cycle of the literal bonus-switch formula.
One copy per original literal occurrence, with no cycle at the one-off b₀.
The source allows any fixed ordering of the occurrences of a variable. -/
namespace Paper5.AlwaysSatOriginal.Physical

variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

abbrev Fibre (w : Var T) := {p : Port E T // owner p=w}

noncomputable def fibreSize (w : Var T) : ℕ := Nat.card (Fibre E T w)

noncomputable def fibreOrder (w : Var T) :
    Fibre E T w ≃ Fin (fibreSize E T w) := by
  classical
  exact Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α:=Fibre E T w)).symm

def fibres : Port E T ≃ (w : Var T) × Fibre E T w where
  toFun p := ⟨owner p,⟨p,rfl⟩⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨w,p,h⟩
    cases h
    rfl

noncomputable def address : Port E T ≃ (w : Var T) × Fin (fibreSize E T w) :=
  (fibres E T).trans (Equiv.sigmaCongrRight (fibreOrder E T))

noncomputable def next : Equiv.Perm (Port E T) :=
  ((address E T).trans (Equiv.sigmaCongrRight (fun w=>finRotate (fibreSize E T w)))).trans
    (address E T).symm

@[simp] theorem address_owner (p : Port E T) : (address E T p).1=owner p := rfl

@[simp] theorem address_next (p : Port E T) :
    address E T (next E T p) =
      ⟨(address E T p).1,finRotate _ (address E T p).2⟩ := by
  simp [next,Equiv.sigmaCongrRight]

@[simp] theorem next_owner (p : Port E T) : owner (next E T p)=owner p := by
  rw [← address_owner E T (next E T p),address_next,address_owner]

@[simp] theorem prev_owner (p : Port E T) : owner ((next E T).symm p)=owner p := by
  simpa only [Equiv.apply_symm_apply] using (next_owner E T ((next E T).symm p)).symm

abbrev OnCycle (p : Port E T) : Prop := owner p≠b₀ T
abbrev Cycle (E : Finset (V×V)) (T : Finset V) := ↥(cycleSlots E T)

theorem mem_cycle_iff (p : Port E T) : p∈cycleSlots E T ↔ OnCycle E T p := by
  classical
  simp [cycleSlots]

theorem cycle_excludes_exactly_bonus0 (p : Port E T) :
    p∈cycleSlots E T ↔ p≠bonusZeroPort E T := by
  rw [mem_cycle_iff]
  change owner p≠b₀ T ↔ _
  exact not_congr (bonus0_unique_port p)

lemma size_at_least_two [DecidableEq V] [Nonempty V]
    (hC : ∀ v,GraphCutMoments.degree E v=3) (w : Var T) (hw : w≠b₀ T) :
    2≤fibreSize E T w := by
  classical
  obtain ⟨p,q,hpq,hp,hq⟩ := two_ports_except_bonus0 E T hC w hw
  have h : Nontrivial (Fibre E T w) :=
    ⟨⟨⟨p,hp⟩,⟨q,hq⟩,fun h=>hpq (congrArg Subtype.val h)⟩⟩
  letI := h
  rw [fibreSize,Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

lemma rotate_ne_self {n : ℕ} (hn : 2≤n) (i : Fin n) : finRotate n i≠i := by
  cases n with
  | zero => omega
  | succ m =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    split at hv
    case isTrue he =>
      have hj := congrArg Fin.val he
      simp only [Fin.val_last] at hj
      omega
    case isFalse => omega

theorem next_ne_self_on_cycle [DecidableEq V] [Nonempty V]
    (hC : ∀ v,GraphCutMoments.degree E v=3) (p : Cycle E T) :
    next E T p.val≠p.val := by
  intro hp
  have h := (address_next E T p.val).symm.trans (congrArg (address E T) hp)
  have hidx := eq_of_heq (Sigma.ext_iff.mp h).2
  exact rotate_ne_self (size_at_least_two E T hC _ ((mem_cycle_iff E T _).mp p.property)) _ hidx

/-- Truth propagates all the way around a finite directed cycle. -/
theorem bool_cycle_constant {n : ℕ} (a : Fin n→Bool)
    (h : ∀ i,a i=true → a (finRotate n i)=true) (i j : Fin n) : a i=a j := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    have forward (v : ℕ) (hv : v<m+1) (u : ℕ) (hu : u≤v)
        (h0 : a ⟨u,by omega⟩=true) : a ⟨v,hv⟩=true := by
      induction v with
      | zero =>
        have hzero : u=0 := by omega
        subst u
        exact h0
      | succ v ih =>
        by_cases he : u=v+1
        · subst u
          exact h0
        · have hvm : v<m := by omega
          have htrue := ih (by omega) (by omega) h0
          have hstep := h ⟨v,by omega⟩ htrue
          rwa [finRotate_of_lt hvm] at hstep
    have everywhere (u : Fin (m+1)) (hu : a u=true) (v : Fin (m+1)) : a v=true := by
      have hlast : a (Fin.last m)=true :=
        forward m (Nat.lt_succ_self m) u.val (Nat.le_of_lt_succ u.isLt) hu
      have h0 := h (Fin.last m) hlast
      rw [finRotate_last] at h0
      exact forward v.val v.isLt 0 (Nat.zero_le _) h0
    by_cases hi : a i=true
    · exact hi.trans (everywhere i hi j).symm
    · by_cases hj : a j=true
      · exact (hi (everywhere j hj i)).elim
      · cases hI : a i <;> cases hJ : a j <;> simp_all

theorem rotates_constant_on_fibre (g : Port E T→Bool)
    (h : ∀ p : Cycle E T,g p.val=true → g (next E T p.val)=true)
    (p q : Port E T) (hpq : owner p=owner q) :
    g p=g q := by
  by_cases hb : owner p=b₀ T
  · have hp := (bonus0_unique_port p).mp hb
    have hq := (bonus0_unique_port q).mp (hpq.symm.trans hb)
    rw [hp,hq]
  · let w := owner p
    let a : Fin (fibreSize E T w)→Bool := fun i=>g ((address E T).symm ⟨w,i⟩)
    have ht (i : Fin (fibreSize E T w)) :
        owner ((address E T).symm ⟨w,i⟩)=w := by
      rw [←address_owner E T,Equiv.apply_symm_apply]
    have hstep (i : Fin (fibreSize E T w)) : a i=true → a (finRotate _ i)=true := by
      intro hi
      let s := (address E T).symm ⟨w,i⟩
      have hc : s∈cycleSlots E T := (mem_cycle_iff E T s).mpr (fun hh=>hb ((ht i).symm.trans hh))
      have hn : next E T s = (address E T).symm ⟨w,finRotate _ i⟩ := by
        apply (address E T).injective
        rw [address_next]
        have hs : address E T s=⟨w,i⟩ := (address E T).apply_symm_apply _
        rw [hs,Equiv.apply_symm_apply]
      change g s=true at hi
      simpa only [hn] using h ⟨s,hc⟩ hi
    let pi := fibreOrder E T w ⟨p,rfl⟩
    let qi := fibreOrder E T w ⟨q,hpq.symm⟩
    have hp : (address E T).symm ⟨w,pi⟩=p := by
      have he : address E T p=⟨w,pi⟩ := rfl
      rw [←he,Equiv.symm_apply_apply]
    have hq : (address E T).symm ⟨w,qi⟩=q := by
      apply (address E T).injective
      rw [Equiv.apply_symm_apply]
      unfold address
      have he : (⟨w,⟨q,hpq.symm⟩⟩ : (w : Var T) × Fibre E T w) =
          ⟨owner q,⟨q,rfl⟩⟩ := (fibres E T).symm.injective rfl
      exact congrArg (Equiv.sigmaCongrRight (fibreOrder E T)) he
    simpa only [a,hp,hq] using bool_cycle_constant a hstep pi qi

#print axioms address_next
#print axioms next_owner
#print axioms prev_owner
#print axioms cycle_excludes_exactly_bonus0
#print axioms size_at_least_two
#print axioms next_ne_self_on_cycle
#print axioms bool_cycle_constant
#print axioms rotates_constant_on_fibre
end Paper5.AlwaysSatOriginal.Physical