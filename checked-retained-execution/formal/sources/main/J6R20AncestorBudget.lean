import J6R20AncestorLiteral

/-! Routing a retained packet is quadratic in its actual local port
count, not in the entire descendant graph. The packet's physical seat
cap supplies an explicit bound for arbitrary serialized port order. -/
namespace J6R20Ancestor
open J6R18ChildWrite J6R10Repack P11FullPacking J6R9PacketScopes

variable {E A B G : Type} [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}

theorem hop_port_cap {H K : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K)
    (k : Page a P.copies G) (stay : grp (.inr k)=h)
    (ps : List (HopPorts grp pkt k stay)) (hn : ps.Nodup) :
    ps.length≤2*2^a := by
  classical
  let e := packetPortsEmbedding N (atGroup P i) P.seat g k
  let f := (packetReindex N (atGroup P i) (atPacket P) g k).trans (Equiv.refl _)
  let y : List (Fin (2^a)×Bool) := ps.map (fun p=>e (f (hop grp pkt k stay p)))
  have hi : Function.Injective (fun p=>e (f (hop grp pkt k stay p))) :=
    e.injective.comp (f.injective.comp (hop grp pkt k stay).injective)
  have hy : y.Nodup := hn.map hi
  calc
    ps.length=y.length := (List.length_map _).symm
    _=y.toFinset.card := (List.toFinset_card_of_nodup hy).symm
    _≤_ := by simpa [Fintype.card_prod,Nat.mul_comm] using Finset.card_le_univ y.toFinset

theorem col_order_max (P : PhysicalPacking N a G) (i : Fin a) (g : G) (k : Page a P.copies G)
    (cs : List (ColsOf P i g k)) (hn : cs.Nodup) :
    cs.length≤2^a := by
  classical
  let f (c : ColsOf P i g k) := (P.seat c.val).2
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply P.seat.injective
    exact Prod.ext (x.property.2.trans y.property.2.symm) h
  let ys := cs.map f
  have hY : ys.Nodup := hn.map hi
  calc
    cs.length=ys.length := (List.length_map _).symm
    _=ys.toFinset.card := (List.toFinset_card_of_nodup hY).symm
    _≤_ := by simpa only [Fintype.card_fin] using Finset.card_le_univ ys.toFinset

theorem routeFee_local_bound (a n r c : ℕ) {L : ℕ} (hn : n≤2*L) (hr : r≤L) (hc : c≤L) :
    routeFee a n r c ≤ 4*L^2*(11*a+13)+2*L*(6*a+24)+6 := by
  calc
    _≤routeFee a (2*L) L L := by
      unfold routeFee tapeFee slotFee findFee
      gcongr
    _=_ := by unfold routeFee tapeFee slotFee findFee portFee; ring

#print axioms hop_port_cap
#print axioms col_order_max
#print axioms routeFee_local_bound
end J6R20Ancestor

