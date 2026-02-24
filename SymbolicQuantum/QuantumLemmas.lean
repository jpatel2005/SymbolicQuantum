import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumDefs
import SymbolicQuantum.QuantumTactics

open QGate QCircuit

lemma Qeval_QRange_succ_split {n start k : ℕ} :
〚QRange_H n start (k + 1)〛 = 〚QRange_H n start k ≫ QRange_H n (start + k) 1〛 := rfl

-- Disjoint commuting lemma for QRange_H
lemma QRange_H_disj_comm {n : ℕ} (start len target : ℕ)
(ht : target < n)
(h_disjoint : target ≥ start + len) :
∀ ψ, 〚QRange_H n start len〛 (〚app (H ⟨target, ht⟩)〛 ψ) =
〚app (H ⟨target, ht⟩)〛 (〚QRange_H n start len〛 ψ) := by {
  induction len generalizing start target ht with
  | zero =>
    simp [QRange_H, Qeval]
  | succ range_len ih =>
    intro ψ
    have h_range_len : start + range_len < n := by omega
    simp [QRange_H,Qeval,h_range_len,Qeval_gate]
    change 〚app (H ⟨start + range_len, h_range_len⟩)〛 (〚QRange_H n start range_len〛 (〚app (H ⟨target, ht⟩)〛 ψ)) =
      〚app (H ⟨target, ht⟩)〛 (〚app (H ⟨start + range_len, h_range_len⟩)〛 (〚QRange_H n start range_len〛 ψ))
    rw [ih start (target) (ht) (by omega)]
    simp [Qeval,Qeval_gate]
    rw [H_comm _ (by simp;omega)]
}

-- QRange can be split in reverse order of definition
lemma Qeval_QRange_succ_split_rev {n start k : ℕ} (h : start + k < n) :
  〚QRange_H n start (k + 1)〛 = 〚QRange_H n (start + k) 1 ≫ QRange_H n start k〛 := by {
  rw [Qeval_QRange_succ_split]
  have hc1 : start + k < n := by omega
  simp [QRange_H, hc1, Qeval, Qeval_gate]
  funext ψ
  change 〚app (H ⟨start + k, h⟩)〛 (〚QRange_H n start k〛 ψ) =
    〚QRange_H n start k〛 (〚app (H ⟨start + k, h⟩)〛 ψ)
  rw [QRange_H_disj_comm]
  exact Nat.le_refl _
}

lemma QRange_H_involutive_general (m n : ℕ) (h_bound : n ≤ m + 1) :
  ∀ (ψ : QState (m + 1)),
  〚QRange_H (m+1) 0 n〛 (〚QRange_H (m+1) 0 n〛 ψ) = ψ := by {
  induction n with
  | zero =>
    intro ψ
    simp [QRange_H, Qeval]
  | succ k ih =>
    intro ψ
    nth_rw 1 [Qeval_QRange_succ_split_rev (by linarith)]
    nth_rw 1 [Qeval]
    have hk : k < m + 1 := by omega
    simp [QRange_H, hk, Qeval, Qeval_gate]
    rw [H_involutive, ih (by omega)]
}

-- QRange_H applied to one state times another is equivalent to applying to
-- one state then multiplying by the other
lemma QRange_H_distrib_disjoint (m k : ℕ) (hk_bound : k ≤ m + 1) :
  ∀ (f g : BitString (m+1) → ℂ),
  (∀ (bs : BitString (m+1)) (v : Qubit) (j : Fin (m+1)),
     (j : ℕ) < k → g (fun i => if i = j then v else bs i) = g bs) →
  〚QRange_H (m + 1) 0 k〛 (fun bs => f bs * g bs)
  = (fun bs => (〚QRange_H (m + 1) 0 k〛 f) bs * g bs) := by {
  induction k with
  | zero =>
    simp [QRange_H, Qeval]
  | succ k' ih =>
    intros f g h_ignore
    have hk' : k' < m + 1 := by omega
    rw [QRange_H]
    simp [hk', Qeval, Qeval_gate]
    rw [ih (by omega) f g]
    {
      funext bs
      have h_inv_at_k : ∀ (v : Qubit), g (fun i ↦ if i = ⟨k', hk'⟩ then v else bs i) = g bs := by {
        intro v
        apply h_ignore bs v ⟨k', hk'⟩
        simp
      }
      simp [app_H, h_inv_at_k]
      cases hk' : bs ⟨k', hk'⟩ <;> ring_nf
    }
    {
      intros bs v j hj
      apply h_ignore bs v j
      exact Nat.lt_succ_of_lt hj
    }
}

lemma QRange_H_distrib_disjoint_gen (k y : ℕ) (hk_bound : k ≤ y) :
  ∀ (f g : BitString y → ℂ),
  (∀ (bs : BitString y) (v : Qubit) (j : Fin y),
     (j : ℕ) < k → g (fun i => if i = j then v else bs i) = g bs) →
  〚QRange_H y 0 k〛 (fun bs => f bs * g bs)
  = (fun bs => (〚QRange_H y 0 k〛 f) bs * g bs) := by {
  induction k with
  | zero =>
    simp [QRange_H, Qeval]
  | succ k' ih =>
    intros f g h_ignore
    have hk' : k' < y := by omega
    rw [QRange_H]
    simp [hk', Qeval, Qeval_gate]
    rw [ih (by omega) f g]
    {
      funext bs
      have h_inv_at_k : ∀ (v : Qubit), g (fun i ↦ if i = ⟨k', hk'⟩ then v else bs i) = g bs := by {
        intro v
        apply h_ignore bs v ⟨k', hk'⟩
        simp
      }
      simp [app_H, h_inv_at_k]
      cases hk' : bs ⟨k', hk'⟩ <;> ring_nf
    }
    {
      intros bs v j hj
      apply h_ignore bs v j
      exact Nat.lt_succ_of_lt hj
    }
}

lemma embed_prefix_ket0n_succ {n : ℕ} :
embed_prefix (ket0n (n + 1)) =
(embed_prefix (embed_prefix (ket0n n))) ⊗[⟨n, by omega⟩] (embed_prefix (embed_last ket0)) := by {
  funext bs
  unfold tensor_product embed_prefix embed_last mask_left mask_right ket0n ket0 basis_state
  simp
  split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
  {
    exfalso
    apply hc3
    funext i
    exact congr_fun hc1 ⟨i, by omega⟩
  }
  {
    exfalso
    apply hc2
    funext x
    exact congr_fun hc1 ⟨n, by omega⟩
  }
  {
    exfalso
    apply hc1
    apply congr_fun at hc4
    apply congr_fun at hc5
    funext k
    by_cases h : k = n
    {
      have : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.eq_of_val_eq h
      rw [this]
      exact hc4 ⟨0, Nat.zero_lt_one⟩
    }
    exact hc5 ⟨k, by omega⟩
  }
}

lemma ket0n_succ_split (m n : ℕ) (h : n < m + 1) :
  embed_arb (by omega) (ket0n (n + 1)) =
  (fun bs => embed_arb (by omega) (ket0n n) bs * ket0 (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  qunfold [π]
  split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
  {
    exfalso
    apply hc3
    funext k
    apply congr_fun at hc1
    rw [←hc1 ⟨k, by omega⟩]
  }
  {
    exfalso
    have : bs ⟨n, h⟩ = Qubit.zero := by
      have := congr_fun hc1
      rw [this ⟨n, Nat.lt_succ_self n⟩]
    apply hc2
    funext k
    rw [this]
  }
  {
    exfalso
    apply hc1
    funext k
    apply congr_fun at hc4
    apply congr_fun at hc5
    by_cases hk : k < n
    { rw [hc5 ⟨k, hk⟩] }
    {
      have hk_eq : k = n := by omega
      simp [hk_eq]
      rw [←hc4 0]
    }
  }
}

lemma ket0n_succ_split_gen (n k : ℕ) (h : n < k) :
  embed_arb (by omega) (ket0n (n + 1)) =
  (fun bs => embed_arb (by omega) (ket0n n) bs * ket0 (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  qunfold [π]
  split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
  {
    exfalso
    apply hc3
    funext k
    apply congr_fun at hc1
    rw [←hc1 ⟨k, by omega⟩]
  }
  {
    exfalso
    have : bs ⟨n, h⟩ = Qubit.zero := by
      have := congr_fun hc1
      rw [this ⟨n, Nat.lt_succ_self n⟩]
    apply hc2
    funext k
    rw [this]
  }
  {
    exfalso
    apply hc1
    funext k
    apply congr_fun at hc4
    apply congr_fun at hc5
    by_cases hk : k < n
    { rw [hc5 ⟨k, hk⟩] }
    {
      have hk_eq : k = n := by omega
      simp [hk_eq]
      rw [←hc4 0]
    }
  }
}

lemma ketPn_succ_split_gen (n k : ℕ) (h : n < k) :
  embed_arb (by omega) (ketPn (n + 1)) =
  (fun bs => embed_arb (by omega) (ketPn n) bs * ketP (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  qunfold [π]
  cases bs ⟨n,h⟩ <;> qsimp [mul_comm]
}

lemma ketPn_succ_split (m n : ℕ) (h : n < m + 1) :
  embed_arb (by omega) (ketPn (n + 1)) =
  (fun bs => embed_arb (by omega) (ketPn n) bs * ketP (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  qunfold [π]
  cases bs ⟨n,h⟩ <;> qsimp [mul_comm]
}

lemma sum_bitstring_split_last (n : ℕ) (ψ : BitString (n + 1) → ℂ) :
  ∑ x : BitString (n + 1), ψ x =
  (∑ x : BitString n, ψ (Fin.snoc x Qubit.zero)) +
  (∑ x : BitString n, ψ (Fin.snoc x Qubit.one)) := by {
  let iso : BitString (n + 1) ≃ BitString n × Qubit := {
    toFun := fun f => (Fin.init f, f (Fin.last n))
    invFun := fun ⟨g, a⟩ => Fin.snoc g a
    left_inv := fun _ => by simp
    right_inv := fun _ => by simp
  }
  calc
    ∑ x : BitString (n + 1), ψ x = ∑ y : BitString n × Qubit, ψ (Fin.snoc y.1 y.2) := by {
      rw [Fintype.sum_equiv iso]
      simp[iso]
    }
    _ = ∑ x : BitString n, ∑ a : Qubit, ψ (Fin.snoc x a) := by rw [Fintype.sum_prod_type]
    _ = ∑ x : BitString n, (ψ (Fin.snoc x Qubit.zero) + ψ (Fin.snoc x Qubit.one)) := by {
      congr
      funext x
      have h_univ : (Finset.univ : Finset Qubit) = {Qubit.zero, Qubit.one} := by
        ext q; cases q <;> simp
      simp [h_univ]
    }
    _ = (∑ x : BitString n, ψ (Fin.snoc x Qubit.zero)) + (∑ x : BitString n, ψ (Fin.snoc x Qubit.one)) := by rw [Finset.sum_add_distrib]
}

/- MATH LEMMAS -/
lemma bs_xor_comm {n : ℕ} (a b : BitString n) : bs_xor a b = bs_xor b a := by {
  funext i
  simp [bs_xor, bxor]
  cases (a i) <;> cases (b i) <;> rfl
}

lemma bs_xor_distrib {n : ℕ} (a b c : BitString n) : bs_xor (bs_xor a b) c = bs_xor a (bs_xor b c) := by {
  funext i
  simp [bs_xor, bxor]
  cases (a i) <;> cases (b i) <;> cases (c i) <;> rfl
}

lemma band_comm (x y : Qubit) : band x y = band y x := by {
  cases x <;> cases y <;> rfl
}

lemma band_bxor_distrib (x y z : Qubit) :
band (bxor x y) z = bxor (band x z) (band y z) := by {
  cases x <;> cases y <;> cases z <;> rfl
}

lemma dot_product_comm {n : ℕ} (x y : BitString n) :
dot_product x y = dot_product y x := by {
  unfold dot_product
  simp
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold dot_product
    simp
    rw [ih, band_comm]
}

lemma bxor_assoc (a b c : Qubit) : bxor (bxor a b) c = bxor a (bxor b c) := by {
  cases a <;> cases b <;> cases c <;> rfl
}

lemma bxor_left_comm (a b c : Qubit) : bxor a (bxor b c) = bxor b (bxor a c) := by {
  cases a <;> cases b <;> cases c <;> rfl
}

-- y·0=0 for any y
lemma dot_product_zero (n : ℕ) (y : BitString n) : dot_product y (fun _ => Qubit.zero) = Qubit.zero := by {
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold dot_product
    simp only []
    rw [ih]
    simp [band, bxor]
}

lemma dot_product_distrib {n : ℕ} (a b c : BitString n) :
  dot_product (bs_xor a b) c = bxor (dot_product a c) (dot_product b c) := by {
  induction n with
  | zero => rfl
  | succ n ih =>
    have band_bxor_distrib (x y z : Qubit) : band (bxor x y) z = bxor (band x z) (band y z) := by {
      cases x <;> cases y <;> cases z <;> rfl
    }
    unfold dot_product
    simp only [bs_xor]
    rw [band_bxor_distrib]
    change bxor (bxor (band (a 0) (c 0)) (band (b 0) (c 0)))
      (dot_product (bs_xor (fun i ↦ a i.succ) (fun i ↦ b i.succ)) (fun i ↦ c i.succ)) = _
    rw [ih]
    simp only [bxor_assoc, bxor_left_comm]
}

lemma bs_xor_self {n : ℕ} (x : BitString n) : bs_xor x x = (fun _ => Qubit.zero) := by {
  funext i
  simp [bs_xor, bxor]
  cases (x i) <;> rfl
}

lemma dot_product_snoc_gen {n : ℕ} (a b : BitString (n + 1)) :
dot_product a b =
bxor (dot_product (fun i => a i.castSucc) (fun i => b i.castSucc)) (band (a (Fin.last n)) (b (Fin.last n))) := by {
  induction n with
  | zero =>
    simp [dot_product, bxor, band]
    cases h0 : a ⟨0, by omega⟩ <;> cases h1 : b ⟨0, by omega⟩ <;> simp_all
  | succ n ih =>
    simp only [dot_product]
    have ih' := ih (fun i => a i.succ) (fun i => b i.succ)
    simp only [dot_product] at ih'
    rw [bxor_assoc, ih', ← bxor_assoc, ← bxor_assoc]
    congr 1
}

lemma dot_product_snoc {k : ℕ} (x : BitString k) (b : Qubit) (y : BitString (k + 1)) :
    dot_product (Fin.snoc x b) y =
    bxor (dot_product x (fun i => y i.castSucc)) (band b (y (Fin.last k))) := by {
  rw [dot_product_snoc_gen (Fin.snoc x b) y]
  congr 2
  · simp [Fin.snoc_castSucc]
  · simp [Fin.snoc_last]
}
