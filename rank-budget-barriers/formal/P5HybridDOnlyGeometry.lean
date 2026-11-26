import J6R9PacketScopes
import P5HybridClosureActual

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000

/-! The two specified coordinates are on one physical four-clone
Appendix D root. Triangle tags attach only to real unary wires; the
other old tables and the subdivision labels remain independent. -/
namespace Paper5.HybridDOnly
open scoped Classical BigOperators
open Paper5.HybridClosure J1MainSourceCollision DiagonalAbundance
open J6R10Repack J6R11CollisionReindex P11FullPacking EmpiricalCutMoments ProductVariance

section Caps

variable {E A B : Type*} [Fintype E] {a : ℕ}
variable (N : Network E A B) (P : PhysicalPacking N a (Fin 64))

theorem native_ordered_cell_load (Δ : ℕ)
    (hΦ : varianceScore (declaredCell N P.rowLabel P.colLabel)≤2*(Nat.card E:ℚ)*Δ)
    (hD : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (c : Draw (Fin a) (Fin 64)) :
    load (J6R11Collision.edgeCell N.row N.col (P.rowLabel,P.colLabel)) c ≤
      2*(Fintype.card E:ℚ)/(Fintype.card (Draw (Fin a) (Fin 64)):ℚ) := by
  let dCell := J6R11Collision.edgeCell N.row N.col (P.rowLabel,P.colLabel)
  have dvar : deviation dCell≤2*(Fintype.card E:ℚ)*Δ := by
    rw [declared_variance_eq N (P.rowLabel,P.colLabel),Nat.card_eq_fintype_card] at hΦ
    exact hΦ
  have dN : 2*(Δ:ℚ)*(Fintype.card (Draw (Fin a) (Fin 64)):ℚ)^2≤Fintype.card E := by
    rw [J6R11Collision.source_word_cells 64 a]
    have hD' : 2*(64^(2*a))^2*Δ≤Fintype.card E := by
      simpa [J9PrintedSchedule.arrayCard,Nat.card_eq_fintype_card,pow_mul,mul_comm,mul_left_comm] using hD
    have hD'' : 2*Δ*(64^(2*a))^2≤Fintype.card E := by
      calc
        _ = 2*(64^(2*a))^2*Δ := by ac_rfl
        _ ≤ _ := hD'
    exact_mod_cast hD''
  exact deviation_load_bound dCell Δ dvar dN c
end Caps

section Original

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => replacedEdges E cubic
local notation "reg" => replaced_cubic E cubic loopless
local notation "N" => dNetwork F reg
local notation "ν" => Fintype.card (TriVertex V)

def innerTie : DOld F→Option V
  | .inr (.inl v) => some v.1
  | _ => none

theorem cloned_inner_slots : (tiedSlots (innerTie E cubic ∘ (N).row)).card=ν := by
  let ι : TriVertex V ↪ DWire F := ⟨_,pinWire_injective E cubic⟩
  have he : tiedSlots (innerTie E cubic ∘ (N).row)=Finset.univ.map ι := by
    ext p
    rcases p with ⟨p,b⟩
    cases b
    · simp [tiedSlots,innerTie,dNetwork,ι,pinWire]
    · rcases p with p|q
      · simp [tiedSlots,innerTie,dNetwork,cloneFactor,ι,pinWire]
      · rcases q with q|q <;> simp [tiedSlots,innerTie,dNetwork,cloneFactor,ι,pinWire]
  rw [he,Finset.card_map,Finset.card_univ]

theorem cloned_inner_fibre (v : V) : (tagFibre (innerTie E cubic ∘ (N).row) v).card=3 := by
  let ι : Fin 3 ↪ DWire F :=
    ⟨fun j=> (Sum.inl (v,j),true),fun _ _ h=>congrArg Prod.snd (Sum.inl.inj (congrArg Prod.fst h))⟩
  have he : tagFibre (innerTie E cubic ∘ (N).row) v=Finset.univ.map ι := by
    ext p
    rcases p with ⟨p,b⟩
    cases b
    · simp [tagFibre,innerTie,dNetwork,ι]
    · rcases p with p|q
      · rcases p with ⟨w,j⟩
        constructor
        · intro h
          have he : w=v := by
            simpa [tagFibre,innerTie,dNetwork,cloneFactor] using h
          subst w
          exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
        · intro h
          obtain ⟨k,_,hk⟩ := Finset.mem_map.mp h
          have he : v=w := congrArg Prod.fst (Sum.inl.inj (congrArg Prod.fst hk))
          subst w
          simp [tagFibre,innerTie,dNetwork,cloneFactor]
      · rcases q with q|q <;> simp [tagFibre,innerTie,dNetwork,cloneFactor,ι]
  rw [he,Finset.card_map,Finset.card_univ,Fintype.card_fin]

theorem literal_row_pin_group {a : ℕ} (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (v : TriVertex V) :
    J6R9PacketScopes.rowGroup P.mask i (P.seat (pinWire E cubic v)) =
      P.rowLabel (.inr (.inl v)) i := by
  exact congrArg (fun c : Cell (Fin a) (Fin 64) => (c i).1)
    (P.exactCell (pinWire E cubic v))

end Original

#print axioms native_ordered_cell_load
#print axioms cloned_inner_slots
#print axioms cloned_inner_fibre
#print axioms literal_row_pin_group
end Paper5.HybridDOnly
