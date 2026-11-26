import P5HybridClosureD
import J6R10RepackPrecision

/-! Real old-row orientation, not the subdivision-as-row J9 interface:
one original clause row per clause, one equality row per clone variable,
and one binary equality column per incidence. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial
open Polynomial J6R10Repack Paper5.HybridClosure

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
local notation "N" => dNetwork F cubic

noncomputable def oldRowTruth (sign : W → Bool) :
    (v : DOld F ⊕ MainClonedCNF.Port F) → (ParentPorts N v → Bool) → Bool
  | .inl (.inl v), x =>
    decide (∀ p q : ParentPorts N (.inl (.inl v)), x p = x q)
  | .inl (.inr (.inl v)), x =>
    decide (x ⟨.inl (.inl v,true),rfl⟩ = sign v)
  | .inl (.inr (.inr (.inl e))), x =>
    x ⟨.inl (.inr (.inl (e,false)),true),rfl⟩ ||
      x ⟨.inl (.inr (.inl (e,true)),true),rfl⟩
  | .inl (.inr (.inr (.inr (v,j)))), x =>
    !(x ⟨.inl (.inr (.inr (v,j,false)),true),rfl⟩) ||
      x ⟨.inl (.inr (.inr (v,j,true)),true),rfl⟩
  | .inr e, x =>
    decide (x ⟨.inr (e,false),rfl⟩ = x ⟨.inr (e,true),rfl⟩)

/-- The table is tagged at the original p, not re-created at p_t. -/
noncomputable def oldRowFile (f : ℤ[X]) (p : ℕ) (sign : W → Bool) : EntryFile f 1 N :=
  fun v => ⟨p, fun x => if oldRowTruth F cubic sign v x then 1 else 0⟩

theorem oldRowFile_creation (f : ℤ[X]) (p : ℕ) (sign : W → Bool)
    (v : DOld F ⊕ MainClonedCNF.Port F) :
    (oldRowFile F cubic f p sign v).created=p := rfl

theorem oldRow_pin_file_congr (f : ℤ[X]) (p : ℕ) (sign sign' : W → Bool) (v : W)
    (h : sign v = sign' v) :
    oldRowFile F cubic f p sign (.inl (.inr (.inl v))) =
      oldRowFile F cubic f p sign' (.inl (.inr (.inl v))) := by
  simp [oldRowFile, oldRowTruth, h]

theorem oldRow_pure_file_congr (f : ℤ[X]) (p : ℕ) (sign sign' : W → Bool)
    (v : DOld F ⊕ MainClonedCNF.Port F)
    (h : ∀ w : W, v ≠ .inl (.inr (.inl w))) :
    oldRowFile F cubic f p sign v = oldRowFile F cubic f p sign' v := by
  rcases v with (k|w|e|c)|e
  · rfl
  · exact False.elim (h w rfl)
  · rfl
  · rfl
  · rfl

#print axioms oldRowFile_creation
#print axioms oldRow_pin_file_congr
#print axioms oldRow_pure_file_congr
end Paper5.D1Literal

