import V8PooledMenuRoot

/-! The tape is indexed by precisely the signed centers of one fixed
active coordinate. No all-coordinate count or extension factor is used. -/
namespace V8NativeMessage
open scoped BigOperators Classical
open V8PooledMenu

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {a M u : ℕ} (hu : 0<u) (huM : u≤M)

abbrev FixedSites (a : ℕ) (i : Fin u) :=
  {t : Center a M u // level hu huM t=i}

def fixedSitesChart (i : Fin u) : FixedSites hu huM a i ≃ ↥(shell a i.val) where
  toFun t := ⟨t.val.val, mem_shell.mpr
    ⟨((active_iff hu huM).mp t.val.property).1,((active_iff hu huM).mp t.val.property).2.1,
      congrArg Fin.val t.property⟩⟩
  invFun z :=
    let h := mem_shell.mp z.property
    let t : Center a M u := ⟨z.val,(active_iff hu huM).mpr ⟨h.1,h.2.1,by rw [h.2.2]; exact i.isLt⟩⟩
    ⟨t,Fin.ext h.2.2⟩
  left_inv t := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

theorem fixedSites_card (hua : u≤a) (i : Fin u) :
    Fintype.card (FixedSites hu huM a i)=2^a/2^i.val := by
  rw [Fintype.card_congr (fixedSitesChart hu huM i),Fintype.card_coe,
    shell_card (i.isLt.le.trans hua)]

/-- The message at each physical signed center has one coefficient
residue for every degree j below its local precision. -/
abbrev FixedTape (a : ℕ) (prec : Fin u → ℕ) (i : Fin u) :=
  (t : FixedSites hu huM a i) → TruncatedProbeMenu.NodeMessage (prec (level hu huM t.val))

def fixedBits (a : ℕ) (i : Fin u) (p : ℕ) := (2^a/2^i.val)*triangle p

theorem fixedTape_card (hua : u≤a) (prec : Fin u → ℕ) (i : Fin u) :
    Fintype.card (FixedTape hu huM a prec i)=2^fixedBits a i (prec i) := by
  rw [Fintype.card_pi]
  have hh (t : FixedSites hu huM a i) :
      Fintype.card (TruncatedProbeMenu.NodeMessage (prec (level hu huM t.val)))=
        2^triangle (prec i) := by
    rw [t.property]
    exact TruncatedProbeMenu.node_message_card (prec i)
  simp only [hh,Finset.prod_const,Finset.card_univ]
  rw [fixedSites_card hu huM hua i,← pow_mul]
  unfold fixedBits
  rw [Nat.mul_comm]

#print axioms fixedSitesChart
#print axioms fixedSites_card
#print axioms fixedTape_card
end
end V8NativeMessage
