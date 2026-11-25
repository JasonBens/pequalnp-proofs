import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8935_1
  (oldMain : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      G.edgeFinset.card + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
          (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 ∧
      ∀ K : Finset (Fin n), IsMinCover (G.deleteEdges ↑(Ustar G C)) K →
        K.card ≤ (tops G C \ centreless G C).card)
  (oneJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      (Ustar G C).Nonempty → (junk G C).card = 1 →
      ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
        K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
  (manyJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    G.IsBipartite → ¬G.IsAcyclic → NoFourCycle G → IsLeastAO G C → TopForm G C →
      (∃ j < C.size, (gateAt C j).op = GateOp.and ∧ ¬BelowF G C j ∧
        ∃ (a b c d : Fin n), G.Adj a b ∧ G.Adj c d ∧ s(a, b) ≠ s(c, d) ∧
          PEqualNP.ReadK.readsAtMost C n [↑a, ↑b] 1 = false ∧
          PEqualNP.ReadK.readsAtMost C n [↑c, ↑d] 1 = false ∧
          gateVal n C j (pairInput a b) = true ∧ gateVal n C j (pairInput c d) = true) →
      (Ustar G C).Nonempty → (junk G C).card ≠ 1 →
      ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
        K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x11 : Finset (Fin x1)), x2.IsVertexCover ↑x11 ∧ x2.edgeFinset.card + x11.card ≤ x4.size + (1 : ℕ)) := by
  classical
  intro n G _ C hB hA h4 hL hT hJ

  have hne : G.edgeFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [SimpleGraph.edgeFinset_eq_empty] at h
    exact hA (h ▸ SimpleGraph.isAcyclic_bot)
  obtain ⟨hcount, hmin⟩ := oldMain n G C h4 hne hL hT
  by_cases hU : (Ustar G C).Nonempty
  · obtain ⟨K, hK, hc⟩ : ∃ K : Finset (Fin n),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
        K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
      by_cases hj : (junk G C).card = 1
      · exact oneJunk n G C h4 hne hL hT hU hj
      · exact manyJunk n G C hB hA h4 hL hT hJ hU hj
    exact ⟨K, fun u v huv => hK u v huv, by omega⟩
  ·
    have hU0 : Ustar G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    let P (m : ℕ) := ∃ K : Finset (Fin n), G.IsVertexCover (↑K) ∧ K.card = m
    have existsP : ∃ m, P m := ⟨_, Finset.univ, by simp [SimpleGraph.IsVertexCover], rfl⟩
    obtain ⟨K, hK, hcard⟩ := Nat.find_spec existsP
    have hKmin : IsMinCover (G.deleteEdges ↑(Ustar G C)) K := by
      rw [hU0, Finset.coe_empty, SimpleGraph.deleteEdges_empty]
      exact ⟨hK, fun T hT => hcard.trans_le (Nat.find_min' existsP ⟨T, hT, rfl⟩)⟩
    have hk := hmin K hKmin
    rw [hU0, Finset.card_empty] at hcount
    exact ⟨K, hK, by omega⟩
