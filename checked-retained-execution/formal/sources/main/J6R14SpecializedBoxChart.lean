import J6R14SpecializedBoxFactors
import J6R11RepackRootEntry

/-! The physical J7/J8 orientation has original unary pins on its
column side. The actual R12 literal J6 root instead has only binary
subdivisions on its column side. No relabeling preserving edges and
column ownership identifies these two original column charts. This does
not exclude transposing/rebuilding the graph or a weighted child. -/
namespace J6R14SpecializedBox
open scoped Classical
open J8Physical

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)

def pinColumnFiber (u : S) : {w : J8Physical.Wire R // colOwner d w = Sum.inl u} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨pinWire d u,by simp [colOwner]⟩
  left_inv w := by
    apply Subtype.ext
    apply d.column.injective
    rw [pinWire_column]
    have hw := w.property
    unfold colOwner at hw
    cases he : d.column w.val with
    | inl p =>
        have hp : p=u := by simpa only [he,Sum.map_inl,id_eq,Sum.inl.injEq] using hw
        simp [hp]
    | inr p => simp [he] at hw
  right_inv _ := rfl

def transportedFiber {E₁ E₂ A₁ A₂ : Type*} (wire : E₁ ≃ E₂) (owner : A₁ ≃ A₂)
    (a₁ : E₁→A₁) (a₂ : E₂→A₂) (h : ∀ e, owner (a₁ e) = a₂ (wire e))
    (v : A₁) :
    {e : E₁ // a₁ e = v} ≃ {e : E₂ // a₂ e = owner v} :=
  Equiv.subtypeEquiv wire (fun e => by rw [← h e]; exact owner.injective.eq_iff.symm)

theorem no_column_preserving_literal_root {Label W : Type*} [LinearOrder Label]
    {a b m q l : ℕ} (T : J6OrientedHost.Plant W m q) (word : Fin a→Label)
    (u : S)
    (wire : J8Physical.Wire R ≃ J6OrientedHost.Wire word m b l)
    (col : (S⊕V) ≃ J6R11Repack.Right word m b l q) :
    ¬ ∀ e, col (colOwner d e) =
      (J6R11Repack.rootNetwork (b:=b) (l:=l) T word).col (wire e) := by
  intro h
  have h₁ := Nat.card_congr (pinColumnFiber d u)
  have h₂ := Nat.card_congr (transportedFiber wire col (colOwner d)
    (J6R11Repack.rootNetwork (b:=b) (l:=l) T word).col h (.inl u))
  have h₃ := J6R11Repack.root_col_degree T word (col (.inl u))
  have hu : Nat.card Unit = 1 := Nat.card_unique
  rw [hu] at h₁
  omega

#print axioms pinColumnFiber
#print axioms transportedFiber
#print axioms no_column_preserving_literal_root
end J6R14SpecializedBox
