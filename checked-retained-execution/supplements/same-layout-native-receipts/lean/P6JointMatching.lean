import P6JointWeights
import J7SeatQuota

namespace Paper6JointSeating
open scoped Classical
open J7SeatQuota

noncomputable section
set_option linter.unusedSectionVars false

variable {W R V C : Type*} [Fintype W] [Fintype C] [DecidableEq W] [DecidableEq C]
variable (p : W → Prop) [DecidablePred p]
variable (row : W → R) (col : W → V) (label : W → C)

theorem matching_from_cell_quota (quota : ℕ) (err : ℚ) (herr : 0 ≤ err)
    (hvar : (Nat.card {w // p w} : ℚ)*5^2 ≤ err^2)
    (degree : ∀ e : {w // p w},
      (J7SeatMatching.nearby (fun x : {w // p w} => row x.val) (fun x => col x.val) e).card ≤ 5)
    (hmargin : ∀ c, (quota : ℚ)+err ≤
      (Nat.card {w : {w // p w} // label w.val = c} : ℚ)*(1/2:ℚ)^5) :
    ∃ matched : Finset W, matched ⊆ Finset.univ.filter p ∧
      Set.InjOn row {w | w ∈ matched} ∧ Set.InjOn col {w | w ∈ matched} ∧
      ∀ c, quota ≤ (ofCell label matched c).card := by
  have hvar' : (Fintype.card {w // p w} : ℚ)*(5:ℚ)^2 ≤ err^2 := by
    simpa only [Nat.card_eq_fintype_card] using hvar
  obtain ⟨g,hr,hc,hq⟩ := finite_quota (fun w : {w // p w} => row w.val) (fun w => col w.val)
    (fun w => label w.val) 5 quota err degree herr hvar' hmargin
  let s : Finset W := Finset.univ.filter (fun w => ∃ h : p w, (⟨w,h⟩ : {w // p w}) ∈ g)
  have hs (w : W) : w ∈ s ↔ ∃ h : p w, (⟨w,h⟩ : {w // p w}) ∈ g := by simp [s]
  refine ⟨s,?_,?_,?_,?_⟩
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((hs w).mp hw).choose⟩
  · intro x hx y hy hxy
    obtain ⟨hx1,hx2⟩ := (hs x).mp hx
    obtain ⟨hy1,hy2⟩ := (hs y).mp hy
    exact congrArg Subtype.val (hr hx2 hy2 hxy)
  · intro x hx y hy hxy
    obtain ⟨hx1,hx2⟩ := (hs x).mp hx
    obtain ⟨hy1,hy2⟩ := (hs y).mp hy
    exact congrArg Subtype.val (hc hx2 hy2 hxy)
  · intro c
    let e : {w : {w : {w // p w} // label w.val = c} // w.val ∈ g} ≃
          {w // w ∈ ofCell label s c} :=
      { toFun := fun w => ⟨w.val.val.val,Finset.mem_filter.mpr
          ⟨(hs _).mpr ⟨w.val.val.prop,w.prop⟩,w.val.prop⟩⟩
        invFun := fun w =>
          let h := Finset.mem_filter.mp w.prop
          let v := (hs _).mp h.1
          ⟨⟨⟨w.val,v.choose⟩,h.2⟩,v.choose_spec⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hp := hq c
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe] at hp
    exact hp

#print axioms matching_from_cell_quota
end
end Paper6JointSeating
