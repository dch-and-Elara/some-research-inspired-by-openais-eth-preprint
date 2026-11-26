import P5AlwaysSatOriginalPhysicalDPack

/-! Tight marginal domination on the real signed-pin sides of the actual
packed (M.7) CNF and quarter-balanced symbol unions at every root coordinate. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
open J6R10Repack J6R11CollisionReindex P11FullPacking
open SourceDensity EmpiricalCutMoments Filter

variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

noncomputable def dPinWord (P : PhysicalPacking (dNetwork E T) (dA E T) (Fin 64))
    (v : V) : Fin (dA E T)→Fin 64 :=
  P.rowLabel ((dNetwork E T).row (dMarked E T v))

theorem d_pin_word_real_seat (P : PhysicalPacking (dNetwork E T) (dA E T) (Fin 64))
    (v : V) (i : Fin (dA E T)) :
    (physicalCell P.mask (P.seat (dMarked E T v)) i).1=dPinWord E T P v i := by
  exact congrArg (fun c : Cell (Fin (dA E T)) (Fin 64)=> (c i).1)
    (P.exactCell (dMarked E T v))

private theorem exact_fibre {X Y : Type*} [Fintype X] [DecidableEq Y] (funct : X→Y) (y : Y) :
    fiberCount funct y=Nat.card {x : X // funct x=y} := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

theorem d_marked_symbol_law [Nonempty V]
    (P : PhysicalPacking (dNetwork E T) (dA E T) (Fin 64))
    (hCap : ∀ c : Cell (Fin (dA E T)) (Fin 64),
      (Nat.card (J6R10Repack.Fiber (declaredCell (dNetwork E T) P.rowLabel P.colLabel) c):ℚ) ≤
        40*(Fintype.card V:ℚ)/dCells E T)
    (i : Fin (dA E T)) (g : Fin 64) :
    empiricalLaw (fun v=>dPinWord E T P v i) g≤(5/8:ℚ) := by
  let area := declaredCell (dNetwork E T) P.rowLabel P.colLabel
  let proj := atEnd (a:=dA E T) i false (G:=Fin 64)
  let k := fiberCount proj g
  let D : ℚ := dCells E T
  let N : ℚ := Fintype.card V
  have hd : 0<D := by dsimp [D,dCells,J9PrintedSchedule.arrayCard]; positivity
  have hn : 0<N := by dsimp [N]; exact_mod_cast Fintype.card_pos (α:=V)
  have hk : D=64*(k:ℚ) := by
    have h : dCells E T=64*k := by
      rw [←d_cells_exact]
      have he : k=Nat.card {c : Cell (Fin (dA E T)) (Fin 64) // proj c=g} :=
        exact_fibre proj g
      rw [he]
      simpa only [Fintype.card_fin] using (side_cell_card i false g).symm
    dsimp only [D]
    exact_mod_cast h
  have hcap (c : Cell (Fin (dA E T)) (Fin 64)) :
      (fiberCount area c:ℚ)≤40*N/D := by
    have h : fiberCount area c=Nat.card {e : DWire E T // area e=c} :=
      exact_fibre area c
    rw [h]
    exact hCap c
  have hproj : (fiberCount (fun e=>proj (area e)) g:ℚ)≤40*N/64 := by
    rw [fiberCount_comp,Nat.cast_sum]
    calc
      _ ≤ ∑ _c ∈ Finset.univ.filter (fun c=>proj c=g),40*N/D :=
        Finset.sum_le_sum (fun c _=>hcap c)
      _ = (k:ℚ)*(40*N/D) := by rw [Finset.sum_const,nsmul_eq_mul]; rfl
      _ = 40*N/64 := by
        apply (eq_div_iff (by decide : (64:ℚ)≠0)).mpr
        calc
          _ = (D*(40*N/D)) := by rw [hk]; ring
          _ = _ := by rw [mul_comm,div_mul_cancel₀ _ hd.ne']
  have hmark : (fiberCount (fun v=>proj (area (dMarked E T v))) g:ℚ)≤
      fiberCount (fun e=>proj (area e)) g := by
    exact_mod_cast fiberCount_injection (dMarked E T) (fun e=>proj (area e)) g
  change (fiberCount (fun v=>proj (area (dMarked E T v))) g:ℚ)/N≤_
  apply (div_le_iff₀ hn).mpr
  have h := hmark.trans hproj
  linarith only [h]

/-- The literal rounded layout and the claimed bound hold uniformly for
every cubic input and every bonus set of size at most floor(N/4), provided
the explicit sufficient root threshold holds. -/
theorem d_actual_balanced [DecidableEq V] [Nonempty V]
    (hC : ∀ v,GraphCutMoments.degree E v=3) (hT : T.card≤Fintype.card V/4)
    (hN : 16≤Fintype.card V) (hLambda : 393216≤Nat.clog 2 (Fintype.card V)) :
    ∃ P : PhysicalPacking (dNetwork E T) (dA E T) (Fin 64),
      P.copies=P11FullPacking.ceilCopies (2^dA E T)
        (J6R10Repack.maxFiber (declaredCell (dNetwork E T) P.rowLabel P.colLabel)) ∧
      (∀ i : Fin (dA E T),∀ g : Fin 64,
        empiricalLaw (fun v=>dPinWord E T P v i) g≤(5/8:ℚ)) ∧
      ∃ group : Fin (dA E T)→Finset (Fin 64), ∀ i,
        (1/4:ℚ)*Fintype.card V ≤
          (min (BalancedUnion.vertexUnion (fun v=>dPinWord E T P v i) (group i)).card
            (Fintype.card V-(BalancedUnion.vertexUnion (fun v=>dPinWord E T P v i) (group i)).card):ℕ) := by
  obtain ⟨P,hP,_,hcap⟩ := d_actual_packing E T hC hT hN (d_mesh_threshold_from_N E T hC hLambda)
  have hm := d_marked_symbol_law E T P hcap
  refine ⟨P,hP,hm,?_⟩
  have h := fun i=>BalancedUnion.exists_balanced_vertex_union_of_law
    (fun v=>dPinWord E T P v i) (fun g=>(hm i g).trans (by norm_num : (5/8:ℚ)≤3/4))
  choose U hU using h
  exact ⟨U,hU⟩

theorem d_uniform_numeric_threshold :
    ∃ N₀ : ℕ, ∀ N≥N₀, 16≤N ∧ 393216≤Nat.clog 2 N := by
  have hlo (k : ℕ) : ∀ᶠ N : ℕ in atTop, k≤Nat.clog 2 N := by
    filter_upwards [eventually_ge_atTop ((2:ℕ)^k)] with N hN
    simpa only [Nat.clog_pow 2 k (by decide : (1:ℕ)<2)] using Nat.clog_mono_right 2 hN
  have h : ∀ᶠ N : ℕ in atTop,16≤N ∧ 393216≤Nat.clog 2 N :=
    (eventually_ge_atTop 16).and (hlo 393216)
  exact eventually_atTop.mp h

#print axioms d_uniform_numeric_threshold
#print axioms d_pin_word_real_seat
#print axioms d_marked_symbol_law
#print axioms d_actual_balanced
end Paper5.AlwaysSatOriginal.Physical