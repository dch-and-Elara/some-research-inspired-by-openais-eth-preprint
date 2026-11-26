import P5HybridClosureDPack

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-! Ordered off-diagonal source pairs from one nonempty tie tag.
Self-pairs are already charged in the endpoint collision census. -/
namespace Paper5.HybridDOnly
open scoped Classical BigOperators
open J1MainSourceCollision

variable {E T : Type*} [Fintype E] [DecidableEq E] [DecidableEq T]

def offTiedPairs (tag : E→Option T) : Finset (E×E) :=
  Finset.univ.filter (fun p=>p.1≠p.2 ∧ ∃ t,tag p.1=some t ∧ tag p.2=some t)

def tiedMates (tag : E→Option T) (e : E) : Finset E :=
  (tag e).elim ∅ (fun t=>(tagFibre tag t).erase e)

theorem mem_tiedMates (tag : E→Option T) (e e' : E) :
    e'∈tiedMates tag e ↔ e≠e' ∧ ∃ t,tag e=some t ∧ tag e'=some t := by
  cases h : tag e <;> simp [tiedMates,tagFibre,h,ne_comm]

theorem off_ties_card_eq_mates (tag : E→Option T) :
    (offTiedPairs tag).card=∑ e : E,(tiedMates tag e).card := by
  have he : offTiedPairs tag=Finset.univ.filter (fun p : E×E=>p.2∈tiedMates tag p.1) := by
    ext p
    simp [offTiedPairs,mem_tiedMates]
  rw [he,Finset.card_filter,Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _=>?_
  have h := Finset.card_filter (s:=(Finset.univ : Finset E))
    (p:=fun e'=>e'∈tiedMates tag e)
  rw [Finset.filter_univ_mem] at h
  exact h.symm

theorem off_ties_card_le (tag : E→Option T) (k n : ℕ)
    (fiber : ∀ t,(tagFibre tag t).card≤k+1) (pins : (tiedSlots tag).card≤n) :
    (offTiedPairs tag).card≤k*n := by
  have h (e : E) : (tiedMates tag e).card≤k*(if e∈tiedSlots tag then 1 else 0) := by
    cases he : tag e with
    | none => simp [tiedMates,he]
    | some t =>
      have hm : e∈tagFibre tag t := by simp [tagFibre,he]
      have hpin : e∈tiedSlots tag := by simp [tiedSlots,he]
      rw [tiedMates,he,Option.elim_some,Finset.card_erase_of_mem hm,if_pos hpin,mul_one]
      exact Nat.sub_le_of_le_add (fiber t)
  have hs : (∑ e : E,if e∈tiedSlots tag then (1:ℕ) else 0)=(tiedSlots tag).card := by
    have w := Finset.card_filter (s:=(Finset.univ : Finset E)) (p:=fun e=>e∈tiedSlots tag)
    rw [Finset.filter_univ_mem] at w
    exact w.symm
  rw [off_ties_card_eq_mates]
  calc
    _ ≤ ∑ e : E,k*(if e∈tiedSlots tag then (1:ℕ) else 0) := Finset.sum_le_sum fun e _=>h e
    _ = k*(tiedSlots tag).card := by rw [← Finset.mul_sum,hs]
    _ ≤ _ := Nat.mul_le_mul_left _ pins

#print axioms mem_tiedMates
#print axioms off_ties_card_eq_mates
#print axioms off_ties_card_le
end Paper5.HybridDOnly
