import J6R12BlueprintReach
import J6R15ModeCostCap

/-! The R15 roster is not a larger artificial alphabet: its crossing
descriptor is equivalent to the mode actually used by the dependent
J6 packet factory. Map the Finsupp menu injectively into the exact
serialized strict-tuple list in any complete descriptor order. -/
namespace J6R16ModeCost
open scoped BigOperators Polynomial Classical
open P11FullPacking J6R9PacketScopes J6R12Blueprint J6ActiveRun J6R10Reachable J6R15ModeCost
open J1PPrinted J6R11Blueprint

theorem degree_columns {A : Type*} (ms : List A) (w z : A→ℕ) :
    weightedDegree (ms.map w) (ms.map z)=(ms.map fun m=>w m*z m).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [weightedDegree,ih]

theorem roster_is_menu_weight {A B : Type*} [Fintype A] [Fintype B]
    (ξ : A≃B) (w : A→ℕ) (wb : B→ℕ) (hW : ∀ a,w a=wb (ξ a))
    (bs : List B) (hb : bs.Nodup) (hAll : ∀ b,b∈bs) (β : A→₀ ℕ) :
    weightedDegree (bs.map wb) (bs.map fun b=>β (ξ.symm b))=
      J6RecursiveMenu.weighted w β := by
  rw [degree_columns]
  have he : bs.toFinset=Finset.univ := by
    ext b
    simp [hAll b]
  rw [← List.sum_toFinset _ hb,he,J6RecursiveMenu.weighted]
  rw [← ξ.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [Equiv.symm_apply_apply,hW]

theorem menu_injects_roster {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (ξ : A≃B) (w : A→ℕ) (wb : B→ℕ) (hW : ∀ a,w a=wb (ξ a)) (hp : ∀ b,0<wb b)
    (bs : List B) (hb : bs.Nodup) (hAll : ∀ b,b∈bs) (p : ℕ) :
    Nat.card ↑(J6RecursiveMenu.menu p w)≤(strictTuples (bs.map wb) p).length := by
  classical
  let T := strictTuples (bs.map wb) p
  have hpot (j : ℕ) (hj : j∈bs.map wb) : 0<j := by
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hj
    exact hp b
  obtain ⟨hn,hT⟩ := strictTuples_exact (bs.map wb) p hpot
  let enc : ↑(J6RecursiveMenu.menu p w) → ↑(T.toFinset) := fun β =>
    ⟨bs.map (fun b=>β.val (ξ.symm b)), List.mem_toFinset.mpr (hT _ |>.mpr ⟨by simp,by
      rw [roster_is_menu_weight ξ w wb hW bs hb hAll]
      exact (J6RecursiveMenu.exact_printed_menu p w (fun a=>(hW a).symm ▸ hp (ξ a)) β.val).mp β.property⟩)⟩
  have hi : Function.Injective enc := by
    intro x y h
    apply Subtype.ext
    ext a
    have hmap : bs.map (fun b=>x.val (ξ.symm b))=bs.map (fun b=>y.val (ξ.symm b)) :=
      congrArg Subtype.val h
    simpa only [Equiv.symm_apply_apply] using (List.map_inj_left.mp hmap (ξ a) (hAll (ξ a)))
  have h := Nat.card_le_card_of_injective enc hi
  rw [Nat.card_eq_fintype_card (α:=↑(T.toFinset)),Fintype.card_coe,List.toFinset_card_of_nodup hn] at h
  exact h

theorem slot_groups_ne_iff {G : Type*} [LinearOrder G] {a b : ℕ}
    (mask : MaskFamily a b G) (i : Fin a) (p : Page a b G) (j : Fin (2^a)) :
    rowGroup mask i (p,j)≠colGroup mask i (p,j) ↔ (p.1.val i).1≠(p.1.val i).2 := by
  unfold rowGroup colGroup physicalCell cell
  dsimp only
  by_cases hk : (p.1.val i).1≠(p.1.val i).2
  · simp only [dif_pos hk]
    cases slotOrient p.1 (mask p.1 p.2) j ⟨i,hk⟩ <;> simp [hk,ne_comm]
  · simp [hk]

def packet_mode_equiv {G : Type*} [LinearOrder G] {a b : ℕ}
    (mask : MaskFamily a b G) (i : Fin a) (p : ℕ) :
    J6R9PacketScopes.Mode i p mask ≃
      J6R15ModeCost.Mode (Crossing (G:=G) (pages:=b) i) (2^(i.val+1)) p where
  toFun m := (⟨m.page,(slot_groups_ne_iff mask i m.page (tileIndex i m.tile)).mp m.hot⟩,m.tile,m.order)
  invFun m := ⟨m.1.val,m.2.1,m.2.2,
    (slot_groups_ne_iff mask i m.1.val (tileIndex i m.2.1)).mpr m.1.property⟩
  left_inv := by rintro ⟨_,_,_,_⟩; rfl
  right_inv := by rintro ⟨⟨_,_⟩,⟨_,_⟩⟩; rfl

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable (sel : Selector S Δ) {c : Call (PhysicalHost f ell)}

abbrev NativeRoster (d : Ready S Δ c) (t : Center S c) :=
  J6R15ModeCost.Mode (Crossing (G:=Fin 64) (pages:=(packing sel d).copies) (centerIndex d t))
    (2^((centerIndex d t).val+1)) (registerPrecision S c t)

def site_mode_equiv (d : Ready S Δ c) (t : Center S c) :
    (shape S Δ sel).Mode c t ≃ NativeRoster sel d t :=
  (Equiv.cast (modeAt_eq S Δ sel d t)).trans
    (packet_mode_equiv (packing sel d).mask (centerIndex d t) (registerPrecision S c t))

theorem site_mode_weight (d : Ready S Δ c) (t : Center S c) (m : (shape S Δ sel).Mode c t) :
    (shape S Δ sel).weight c t m=modeWeight (site_mode_equiv sel d t m) := by
  let x := Equiv.cast (modeAt_eq S Δ sel d t) m
  have H := weightAt_mode S Δ sel d t x
  simpa only [x,Equiv.symm_apply_apply] using H

theorem site_menu_count (d : Ready S Δ c) (t : Center S c)
    (bs : List (NativeRoster sel d t)) (hb : bs.Nodup) (hAll : ∀ b,b∈bs) :
    Nat.card (NativeMenu (shape S Δ sel) c t)≤
      (strictTuples (bs.map modeWeight) (registerPrecision S c t)).length := by
  letI : Fintype ((shape S Δ sel).Mode c t) := (shape S Δ sel).finiteMode c t
  letI : DecidableEq ((shape S Δ sel).Mode c t) := (shape S Δ sel).decideMode c t
  exact menu_injects_roster (site_mode_equiv sel d t) (shape S Δ sel |>.weight c t) modeWeight
    (site_mode_weight sel d t) (fun m => (modeWeight_bounds m).1) bs hb hAll _

#print axioms degree_columns
#print axioms menu_injects_roster
#print axioms packet_mode_equiv
#print axioms site_mode_weight
#print axioms site_menu_count
end J6R16ModeCost


