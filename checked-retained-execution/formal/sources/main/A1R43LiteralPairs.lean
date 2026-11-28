import P11FullPackingChart
import J6R10RepackPhysical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7800000
set_option maxRecDepth 1400

/-! Physical, genuinely adjacent seats in a pair of equal-symbol
coordinate-zero positions. Construct slots by extending the ordinary
printed template by one cold coordinate. Arbitrary cell chart order
is used only before the extension, not to assert adjacency. -/
namespace A1R43Literal
open scoped Classical
open P11FullPacking
noncomputable section

variable {a b : ℕ}
abbrev Sym := Fin 64

def coldExtend (g : Sym) (c : Cell (Fin a) Sym) : Cell (Fin (a+1)) Sym :=
  Fin.cases (g,g) c

theorem coldExtend_injective (g : Sym) : Function.Injective (@coldExtend a g) := by
  intro c c' e
  funext i
  exact congrFun e i.succ

def extendKey (g : Sym) (k : Key (Fin a) Sym) : Key (Fin (a+1)) Sym :=
  ⟨coldExtend g k.val,Fin.cases le_rfl k.property⟩

def hotRise (g : Sym) (k : Key (Fin a) Sym) : Hot k ≃ Hot (extendKey g k) where
  toFun u := ⟨u.val.succ,u.property⟩
  invFun u := by
    rcases u with ⟨j,h⟩
    induction j using Fin.cases with
    | zero => exact (h rfl).elim
    | succ i => exact ⟨i,h⟩
  left_inv _ := rfl
  right_inv u := by
    rcases u with ⟨j,h⟩
    induction j using Fin.cases with
    | zero => exact (h rfl).elim
    | succ _ => rfl

def extendPage (g : Sym) (p : Page a b Sym) : Page (a+1) b Sym :=
  ⟨extendKey g p.1,(p.2.1,p.2.2 ∘ (hotRise g p.1).symm)⟩

theorem extendPage_injective (g : Sym) : Function.Injective (@extendPage a b g) := by
  rintro ⟨k,u⟩ ⟨j,v⟩ e
  have hj : k=j := Subtype.ext (coldExtend_injective g
    (congrArg (fun (p : Page (a+1) b Sym)=>p.1.val) e))
  subst j
  have q : (u.1,u.2 ∘ (hotRise g k).symm)=(v.1,v.2 ∘ (hotRise g k).symm) := by
    have he := (Sigma.mk.inj_iff.mp e).2
    exact eq_of_heq he
  have uv : u=v := by
    refine Prod.ext ?_ ?_
    · exact congrArg (fun z : Fin b × Orient (extendKey g k)=>z.1) q
    · funext x
      have eq := congrFun (congrArg Prod.snd q) (hotRise g k x)
      simpa [Function.comp_def] using eq
  rw [uv]

def doubleSlot (x : Fin (2^a)) (right : Bool) : Fin (2^(a+1)) :=
  ⟨2*x.val+(if right then 1 else 0),by
    rw [pow_succ]
    have hx := x.isLt
    cases right <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega⟩

theorem doubleSlot_high (x : Fin (2^a)) (b : Bool) (i : Fin a) :
    bits (a+1) (doubleSlot x b) i.succ = bits a x i := by
  unfold bits doubleSlot
  rw [Fin.val_succ,Nat.testBit_succ]
  congr 1
  change (2*x.val+(if b then 1 else 0))/2=x.val
  cases b
  · change (2*x.val+0)/2=x.val
    omega
  · change (2*x.val+1)/2=x.val
    omega

theorem doubleSlot_injective : Function.Injective
    (fun xb : Fin (2^a)×Bool=>doubleSlot xb.1 xb.2) := by
  rintro ⟨x,b⟩ ⟨y,c⟩ eq
  have h := congrArg Fin.val eq
  change 2*x.val+(if b then 1 else 0)=2*y.val+(if c then 1 else 0) at h
  cases b <;> cases c <;> simp_all <;> try omega

def zeroMask (a b : ℕ) : MaskFamily a b Sym := fun _ _ _=>false

def doublePhysical (g : Sym) (s : Physical a b Sym) (d : Bool) : Physical (a+1) b Sym :=
  (extendPage g s.1,doubleSlot s.2 d)

theorem doublePhysical_injective (g : Sym) : Function.Injective
    (fun p : Physical a b Sym×Bool=>doublePhysical g p.1 p.2) := by
  rintro ⟨⟨p,x⟩,d⟩ ⟨⟨q,y⟩,e⟩ h
  have pk : p=q := extendPage_injective g (congrArg Prod.fst h)
  have se : (x,d)=(y,e) := doubleSlot_injective (congrArg Prod.snd h)
  exact Prod.ext (Prod.ext pk (congrArg (fun v : Fin (2^a)×Bool=>v.1) se))
    (congrArg (fun v : Fin (2^a)×Bool=>v.2) se)

theorem doublePhysical_step (g : Sym) (s : Physical a b Sym) :
    (doublePhysical g s true).1=(doublePhysical g s false).1 ∧
      (doublePhysical g s false).2.val+1=(doublePhysical g s true).2.val :=
  ⟨rfl,rfl⟩

theorem physicalCell_double (g : Sym) (s : Physical a b Sym) (d : Bool) :
    physicalCell (zeroMask (a+1) b) (doublePhysical g s d) =
      coldExtend g (physicalCell (zeroMask a b) s) := by
  rcases s with ⟨⟨k,u,o⟩,x⟩
  funext i
  induction i using Fin.cases with
  | zero =>
    simp [physicalCell,cell,doublePhysical,extendPage,extendKey,coldExtend]
  | succ i =>
    have hkey : (extendKey g k).val i.succ=k.val i := rfl
    by_cases h : (k.val i).1 ≠ (k.val i).2
    · have h' : ((extendKey g k).val i.succ).1≠((extendKey g k).val i.succ).2 := h
      unfold physicalCell doublePhysical cell
      change (if h0 : ((extendKey g k).val i.succ).1≠((extendKey g k).val i.succ).2
              then (if slotOrient (extendKey g k) (zeroMask _ _ _ _)
                 (doubleSlot x d) ⟨i.succ,h0⟩ then _ else _) else _) =
            (if h0 : (k.val i).1≠(k.val i).2 then
              (if slotOrient k (zeroMask _ _ _ _) x ⟨i,h0⟩ then _ else _) else _)
      rw [dif_pos h',dif_pos h]
      have bitsEq :
          slotOrient (extendKey g k) (fun _=>false) (doubleSlot x d) ⟨i.succ,h'⟩ =
          slotOrient k (fun _=>false) x ⟨i,h⟩ := by
        unfold slotOrient shiftMask
        exact congrArg (fun z : Bool=>if z then !false else false) (doubleSlot_high x d i)
      rw [show zeroMask _ _ _ _ = (fun _=>false) from rfl,
          show zeroMask _ _ _ _ = (fun _=>false) from rfl,bitsEq]
      rfl
    · simp [physicalCell,doublePhysical,extendPage,cell,coldExtend,hkey,h]

#print axioms coldExtend_injective
#print axioms extendPage_injective
#print axioms doubleSlot_high
#print axioms doublePhysical_injective
#print axioms doublePhysical_step
#print axioms physicalCell_double
end
end A1R43Literal
