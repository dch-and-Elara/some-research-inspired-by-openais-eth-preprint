import A4R45ColumnNames

/-! The actual selected wire order has exactly the original planted taps.
Every designated column gives both wires to hard clauses, so no filler
negative unary can draw from one of those columns. -/
namespace A4R45SourceTaps
open Acquisition AAcquisitionCost P11FullPacking
open A4R45LiteralNetwork A4R45FullCell A4R45ActualPairs A4R45PlantedLabels
open A4R45HardPairs A4R45ColumnNames
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000

noncomputable section
variable {E V₂ V₃ G : Type} [LinearOrder G] {a copies : ℕ}
variable [Fintype E] [Fintype V₂] [Fintype V₃]
variable (word : Fin a→G) (half : ℕ)
local notation "Uplus" => More (V₂:=V₂) (V₃:=V₃) (U:=E⊕V₃) word half
local notation "Wplus" => Wire V₂ V₃ Uplus
local notation "Cols" => columnNames (E:=E) (V₂:=V₂) (V₃:=V₃) word half

def side₂ (actual : (V₂×Fin 2)⊕(V₃×Fin 3) ≃ E×Bool) (v : V₂) (j : Fin 2) : E :=
  (actual (.inl (v,j))).1
def side₃ (actual : (V₂×Fin 2)⊕(V₃×Fin 3) ≃ E×Bool) (v : V₃) (j : Fin 3) : E :=
  (actual (.inr (v,j))).1

def isHardRow : CoverRow V₂ V₃ Uplus → Bool
  | .inr (.inr (.inr _)) => false
  | _ => true

theorem actual_hard_row_by_type (actual : (V₂×Fin 2)⊕(V₃×Fin 3) ≃ E×Bool)
    (h : HPort V₂ V₃) :
    isHardRow word half (embedOriginal word half (reservePair actual (h,true))).1.1=true := by
  rcases h with ⟨v,j⟩|⟨v,j|b⟩
  · rfl
  · rfl
  · cases b <;> rfl

variable (actual : (V₂×Fin 2)⊕(V₃×Fin 3) ≃ E×Bool)
variable (seat : A4R45LiteralNetwork.Wire V₂ V₃ (More (V₂:=V₂) (V₃:=V₃) (U:=E⊕V₃) word half) ≃ Physical a copies G)
variable (pair : ∀ h : HPort V₂ V₃, wirePred seat
    (embedOriginal word half (reservePair actual (h,true))) =
    some (embedOriginal word half (reservePair actual (h,false))))

include pair

theorem literal_hard_read (h : HPort V₂ V₃) :
    (wirePred seat (embedOriginal word half (reservePair actual (h,true)))).map
      (Cols ∘ (Prod.fst : Wplus → Var V₂ V₃ Uplus)) =
        some (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl) (collar actual h).1) := by
  rw [pair h]
  exact congrArg some (columnName_designated word half (collar actual h).1)

theorem unary_never_consumes_designated (u : Uplus) (w : Wplus)
    (hit : wirePred seat (unaryWire u)=some w) :
    ∃ c : OtherColumn (E:=E) (V₂:=V₂) (V₃:=V₃) word half,
      Cols w.1=.inr (.inr c) := by
  classical
  have notHit : w.1∉Set.range (designatedColumn (V₂:=V₂) word half) := by
    rintro ⟨e,he⟩
    obtain ⟨h,hh⟩ := both_designated_wires_are_used (V₂:=V₂) actual e w.2
    have eq : embedOriginal word half (reservePair actual (h,false))=w := by
      rw [hh]
      exact Prod.ext he rfl
    have found := pair h
    rw [eq] at found
    have problem := wirePred_nonreuse seat hit found
    have test := congrArg (fun w : Wplus => isHardRow word half w.1.1) problem
    simp only [actual_hard_row_by_type word half actual h] at test
    change false=true at test
    cases test
  exact ⟨⟨w.1,notHit⟩,columnName_other word half ⟨w.1,notHit⟩⟩

theorem actual_cover_taps :
    ∀ (r : CoverRow V₂ V₃ Uplus) (j : CoverPort r),
      (wirePred seat (⟨r,j⟩,true)).map (Cols ∘ (Prod.fst : Wplus → Var V₂ V₃ Uplus)) =
        coverSources (side₂ actual) (side₃ actual) (compiledStray seat Cols) r j := by
  intro r j
  rcases r with r|r
  · exact literal_hard_read word half actual seat pair (.inl (r,j))
  rcases r with r|r
  · rcases j with j|j
    · exact literal_hard_read word half actual seat pair (.inr (r,.inl j))
    · cases j
      exact literal_hard_read word half actual seat pair (.inr (r,.inr false))
  rcases r with r|u
  · cases j
    exact literal_hard_read word half actual seat pair (.inr (r,.inr true))
  · cases j
    exact compiledStray_filler seat Cols u (fun w hit =>
      unary_never_consumes_designated word half actual seat pair u w hit)

#print axioms actual_hard_row_by_type
#print axioms literal_hard_read
#print axioms unary_never_consumes_designated
#print axioms actual_cover_taps
end
end A4R45SourceTaps
