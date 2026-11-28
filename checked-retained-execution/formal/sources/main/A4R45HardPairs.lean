import A4R45LiteralNetwork

/-! Each true hard-clause occurrence gets a distinct reserved preceding
wire of its intended equality subdivision. Every designated subdivision
supplies both wires, one to each of its two actual hard occurrences. -/
namespace A4R45HardPairs
open Acquisition A4R45LiteralNetwork
set_option autoImplicit false
set_option warningAsError true

variable {V₂ V₃ E : Type*}
abbrev HPort (V₂ V₃ : Type*) := (V₂×Fin 2) ⊕ (V₃×(Fin 3⊕Bool))
abbrev DVar (V₂ V₃ E : Type*) := Var V₂ V₃ (E⊕V₃)
abbrev DWire (V₂ V₃ E : Type*) := Wire V₂ V₃ (E⊕V₃)

def hardOcc : HPort V₂ V₃ → DVar V₂ V₃ E
  | .inl (v,j) => ⟨.inl v,j⟩
  | .inr (v,.inl j) => ⟨.inr (.inl v),.inl j⟩
  | .inr (v,.inr false) => ⟨.inr (.inl v),.inr ()⟩
  | .inr (v,.inr true) => ⟨.inr (.inr (.inl v)),()⟩

def recognizeHard : DVar V₂ V₃ E → Option (HPort V₂ V₃)
  | ⟨.inl v,j⟩ => some (.inl (v,j))
  | ⟨.inr (.inl v),.inl j⟩ => some (.inr (v,.inl j))
  | ⟨.inr (.inl v),.inr _⟩ => some (.inr (v,.inr false))
  | ⟨.inr (.inr (.inl v)),_⟩ => some (.inr (v,.inr true))
  | ⟨.inr (.inr (.inr _)),_⟩ => none

theorem recognized_by_type (h : HPort V₂ V₃) :
    recognizeHard (hardOcc (E:=E) h)=some h := by
  rcases h with ⟨v,j⟩|⟨v,j|b⟩
  · rfl
  · rfl
  cases b <;> rfl

def designated (e : E⊕V₃) : DVar V₂ V₃ E := ⟨.inr (.inr (.inr e)),()⟩

theorem designated_injective : Function.Injective (designated (V₂:=V₂) (V₃:=V₃) (E:=E)) := by
  intro x y h
  have e := congrArg Sigma.fst h
  exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj e))

def collar (actual : ((V₂×Fin 2)⊕(V₃×Fin 3)) ≃ E×Bool) :
    HPort V₂ V₃ ≃ (E⊕V₃)×Bool where
  toFun
    | .inl (v,j) => let q:=actual (.inl (v,j)); (.inl q.1,q.2)
    | .inr (v,.inl j) => let q:=actual (.inr (v,j)); (.inl q.1,q.2)
    | .inr (v,.inr b) => (.inr v,b)
  invFun
    | (.inl e,b) =>
      match actual.symm (e,b) with
      | .inl (v,j) => .inl (v,j)
      | .inr (v,j) => .inr (v,.inl j)
    | (.inr v,b) => .inr (v,.inr b)
  left_inv h := by
    rcases h with ⟨v,j⟩|⟨v,j|b⟩
    · dsimp only
      rw [actual.symm_apply_apply]
    · dsimp only
      rw [actual.symm_apply_apply]
    · rfl
  right_inv h := by
    rcases h with ⟨e|v,b⟩
    · dsimp only
      have he := actual.apply_symm_apply (e,b)
      rcases hj : actual.symm (e,b) with ⟨v,j⟩|⟨v,j⟩ <;>
        rw [hj] at he <;> simp [he]
    · rfl

def endpoints (actual : ((V₂×Fin 2)⊕(V₃×Fin 3)) ≃ E×Bool) :
    HPort V₂ V₃×Bool → DWire V₂ V₃ E
  | (h,true) => (hardOcc h,true)
  | (h,false) => (designated (collar actual h).1,(collar actual h).2)

theorem all_required_pairs_disjoint
    (actual : ((V₂×Fin 2)⊕(V₃×Fin 3)) ≃ E×Bool) :
    Function.Injective (endpoints actual) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ eq
  have eq₁ := congrArg Prod.fst eq
  have hrec := congrArg (recognizeHard (V₂:=V₂) (V₃:=V₃) (E:=E)) eq₁
  cases a <;> cases b
  · have h₁ : (collar actual i).1=(collar actual j).1 := designated_injective eq₁
    have h₂ : (collar actual i).2=(collar actual j).2 :=
      congrArg (fun x : DWire V₂ V₃ E => x.2) eq
    have h := (collar actual).injective (Prod.ext h₁ h₂)
    cases h
    rfl
  · change none=recognizeHard (hardOcc (E:=E) j) at hrec
    rw [recognized_by_type] at hrec
    cases hrec
  · change recognizeHard (hardOcc (E:=E) i)=none at hrec
    rw [recognized_by_type] at hrec
    cases hrec
  · have q : some i=some j := by simpa only [endpoints,recognized_by_type] using hrec
    obtain rfl := Option.some.inj q
    rfl

def reservePair (actual : ((V₂×Fin 2)⊕(V₃×Fin 3)) ≃ E×Bool) :
    HPort V₂ V₃×Bool ↪ DWire V₂ V₃ E :=
  ⟨endpoints actual,all_required_pairs_disjoint actual⟩

theorem hard_pair_quota [Fintype E] [Fintype V₂] [Fintype V₃]
    (actual : ((V₂×Fin 2)⊕(V₃×Fin 3)) ≃ E×Bool) :
    Fintype.card (HPort V₂ V₃)=2*(Fintype.card E+Fintype.card V₃) := by
  rw [Fintype.card_congr (collar actual),Fintype.card_prod,Fintype.card_sum,Fintype.card_bool,mul_comm]

theorem both_designated_wires_are_used
    (actual : ((V₂×Fin 2)⊕(V₃×Fin 3)) ≃ E×Bool) (e : E⊕V₃) (b : Bool) :
    ∃ h : HPort V₂ V₃, reservePair actual (h,false)=(designated e,b) := by
  refine ⟨(collar actual).symm (e,b),?_⟩
  change (designated (collar actual ((collar actual).symm (e,b))).1,
    (collar actual ((collar actual).symm (e,b))).2)=(designated e,b)
  rw [Equiv.apply_symm_apply]

#print axioms recognized_by_type
#print axioms collar
#print axioms all_required_pairs_disjoint
#print axioms hard_pair_quota
#print axioms both_designated_wires_are_used
end A4R45HardPairs
