import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

/-! Explicit hole-free common packet array used by J6.
Each planted wire type occupies one whole distinguished packet. Each
remaining packet is filled by negative unary padding gadgets, two ports
per gadget. Neither isolation nor equal cell loads are assumptions. -/
namespace J6PhysicalPacking
variable {C : Type*} [DecidableEq C]

def offset (rho : C) (m : ℕ) (c : C) := if c = rho then m else 0
abbrev Pad (rho : C) (m K l : ℕ) := Σ c : C, Fin (K-offset rho m c) × Fin l
abbrev Wire (rho : C) (m K l : ℕ) := (Fin m × Fin (2*l)) ⊕ (Pad rho m K l × Bool)
abbrev Slot (C : Type*) (K l : ℕ) := C × (Fin K × Fin (2*l))

theorem offset_le (rho : C) (m : ℕ) (c : C) : offset rho m c ≤ m := by
  unfold offset
  split <;> omega

def siteBit (z : Bool) : ℕ := if z then 1 else 0

def place (rho : C) (m K l : ℕ) (h : m ≤ K) : Wire rho m K l → Slot C K l
  | .inl (i,j) => (rho,Fin.castLE h i,j)
  | .inr (p,b) =>
      (p.1,⟨offset rho m p.1+p.2.1.val,by
        have ht := p.2.1.isLt
        have he := (offset_le rho m p.1).trans h
        omega⟩,⟨2*p.2.2.val+siteBit b,by
        have hb := p.2.2.isLt
        cases b <;> first | (simp [siteBit]; omega) | simp [siteBit]⟩)

theorem place_plant (rho : C) (m K l : ℕ) (h : m ≤ K) (i : Fin m) (j : Fin (2*l)) :
    place rho m K l h (.inl (i,j)) = (rho,Fin.castLE h i,j) := rfl

theorem place_pad_gap (rho : C) (m K l : ℕ) (h : m ≤ K)
    (p : Pad rho m K l) (b : Bool) :
    offset rho m p.1 ≤ (place rho m K l h (.inr (p,b))).2.1.val := by
  simp [place]

theorem place_injective (rho : C) (m K l : ℕ) (h : m ≤ K) :
    Function.Injective (place rho m K l h) := by
  rintro (⟨i,j⟩|⟨p,b⟩) (⟨i',j'⟩|⟨p',b'⟩) he
  · apply congrArg Sum.inl
    exact Prod.ext (Fin.ext (congrArg (fun s : Slot C K l => s.2.1.val) he))
      (congrArg (fun s : Slot C K l => s.2.2) he)
  · have hc : rho = p'.1 := congrArg Prod.fst he
    have hi := i.isLt
    have hh := congrArg (fun s : Slot C K l => s.2.1.val) he
    change i.val = offset rho m p'.1 + p'.2.1.val at hh
    simp [offset,← hc] at hh
    omega
  · have hc : rho = p.1 := (congrArg Prod.fst he).symm
    have hi := i'.isLt
    have hh := congrArg (fun s : Slot C K l => s.2.1.val) he
    change offset rho m p.1 + p.2.1.val = i'.val at hh
    simp [offset,← hc] at hh
    omega
  · rcases p with ⟨c,packet,loc⟩
    rcases p' with ⟨d,packet',loc'⟩
    have hc : c = d := congrArg Prod.fst he
    subst d
    have he₁ := congrArg (fun s : Slot C K l => s.2.1.val) he
    have he₂ := congrArg (fun s : Slot C K l => s.2.2.val) he
    change offset rho m c + packet.val = offset rho m c + packet'.val at he₁
    change 2*loc.val+siteBit b = 2*loc'.val+siteBit b' at he₂
    have hp : packet = packet' := Fin.ext (by omega)
    have hi : loc=loc' := Fin.ext (by cases b <;> cases b' <;> simp [siteBit] at he₂ <;> omega)
    have hb : b=b' := by cases b <;> cases b' <;> simp_all [siteBit]
    subst packet'
    subst loc'
    subst b'
    rfl

theorem place_surjective (rho : C) (m K l : ℕ) (h : m ≤ K) :
    Function.Surjective (place rho m K l h) := by
  rintro ⟨c,k,j⟩
  by_cases he : c=rho ∧ k.val<m
  · obtain ⟨rfl,hk⟩ := he
    refine ⟨Sum.inl (⟨k.val,hk⟩,j),?_⟩
    rfl
  · have hstart : offset rho m c ≤ k.val := by
      unfold offset
      split <;> rename_i hh
      · have hn : ¬ k.val<m := fun ht => he ⟨hh,ht⟩
        omega
      · omega
    have hk := k.isLt
    have hj := j.isLt
    let q : Fin (K-offset rho m c) := ⟨k.val-offset rho m c,by omega⟩
    let v : Fin l := ⟨j.val/2,by omega⟩
    let side : Bool := decide (j.val % 2 = 1)
    refine ⟨Sum.inr (⟨c,(q,v)⟩,side),Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))⟩
    · change offset rho m c+(k.val-offset rho m c)=k.val
      omega
    · change 2*(j.val/2)+siteBit side = j.val
      by_cases hs : j.val%2=1 <;> simp [side,siteBit,hs] <;> omega

noncomputable def placement (rho : C) (m K l : ℕ) (h : m ≤ K) :
    Wire rho m K l ≃ Slot C K l :=
  Equiv.ofBijective _ ⟨place_injective rho m K l h,place_surjective rho m K l h⟩

/-- All real ports at any ordered cell occupy exactly K full packets. -/
theorem uniform_cell [Fintype C] (rho : C) (m K l : ℕ) (h : m ≤ K) (c : C) :
    (Finset.univ.filter (fun w : Wire rho m K l => (place rho m K l h w).1 = c)).card = K*(2*l) := by
  classical
  let e := placement rho m K l h
  let F := Finset.univ.filter (fun w : Wire rho m K l => (place rho m K l h w).1 = c)
  let f : ↥F ≃ (Fin K × Fin (2*l)) := {
    toFun := fun w => (e w.val).2
    invFun := fun p => ⟨e.symm (c,p),by
      have hh := congrArg Prod.fst (e.apply_symm_apply (c,p))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩
    left_inv := fun w => Subtype.ext (e.injective (by
      rw [e.apply_symm_apply]
      exact Prod.ext (Finset.mem_filter.mp w.property).2.symm rfl))
    right_inv := fun p => congrArg Prod.snd (e.apply_symm_apply (c,p)) }
  calc
    F.card = Fintype.card F := (Fintype.card_coe F).symm
    _ = Fintype.card (Fin K × Fin (2*l)) := Fintype.card_congr f
    _ = K*(2*l) := by simp

def reaches {K l : ℕ} (t : ℕ) (p q : Slot C K l) : Prop :=
  p.1=q.1 ∧ p.2.1=q.2.1 ∧ p.2.2.val+t=q.2.2.val

/-- Every genuine positive shift between planted ports is the complete
identity wire type in the layer at offset t. -/
theorem reaches_plant_plant (rho : C) (m K l : ℕ) (h : m ≤ K) (t : ℕ)
    (i i' : Fin m) (j j' : Fin (2*l)) :
    reaches t (place rho m K l h (.inl (i,j))) (place rho m K l h (.inl (i',j'))) ↔
      i=i' ∧ j.val+t=j'.val := by
  constructor
  · rintro ⟨_,hi,hj⟩
    exact ⟨Fin.ext (congrArg (fun f : Fin K => f.val) hi),hj⟩
  · rintro ⟨rfl,hj⟩
    exact ⟨rfl,rfl,hj⟩

/-- No planted packet shares any seat with a padding packet, so no
zero-mode partial shift can link the two types in either direction. -/
theorem no_plant_pad_reach (rho : C) (m K l : ℕ) (h : m ≤ K) (t : ℕ)
    (i : Fin m) (j : Fin (2*l)) (p : Pad rho m K l) (b : Bool) :
    ¬ reaches t (place rho m K l h (.inl (i,j))) (place rho m K l h (.inr (p,b))) ∧
    ¬ reaches t (place rho m K l h (.inr (p,b))) (place rho m K l h (.inl (i,j))) := by
  have key (hc : rho = p.1) (hk : i.val=offset rho m p.1+p.2.1.val) : False := by
    have hi := i.isLt
    simp [offset,←hc] at hk
    omega
  constructor
  · rintro ⟨hc,hk,_⟩
    exact key hc (congrArg Fin.val hk)
  · rintro ⟨hc,hk,_⟩
    exact key hc.symm (congrArg Fin.val hk.symm)

#print axioms placement
#print axioms uniform_cell
#print axioms reaches_plant_plant
#print axioms no_plant_pad_reach
end J6PhysicalPacking
