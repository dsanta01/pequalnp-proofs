import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17902 : ∀ (x1 x2 x3 : (Fin (10 : ℕ) → Bool) → Bool), (∀ (x4 : Fin (10 : ℕ) → Bool), x1 x4 = Bool.false → x2 x4 = Bool.false ∧ x3 x4 = Bool.false) → (¬∃ (x5 : Fin (10 : ℕ) → Bool), x1 x5 = Bool.true ∧ x2 x5 = Bool.false ∧ x3 x5 = Bool.false) → ∀ (x6 : Fin (10 : ℕ) → Bool), x1 x6 = (x2 x6 || x3 x6) := by
  intro f g h hf hn x
  cases hx : f x
  · obtain ⟨hg, hh⟩ := hf x hx
    simp [hg, hh]
  · cases hg : g x <;> cases hh : h x
    · exact absurd ⟨x, hx, hg, hh⟩ hn
    all_goals rfl
