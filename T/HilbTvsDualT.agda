module T.HilbTvsDualT where

open import Relation.Binary.PropositionalEquality
open import Basics
open import T.HilbertT
open import T.DualT

-- Proof of equivalence of Hilbert T with dual-context system T.

dual-s : ∀ {Δ Γ A B C} -> Δ / Γ ⊢ (A => B => C) => (A => B) => (A => C)
dual-s =  DT-lam (DT-lam (DT-lam
  (DT-app (DT-app (DT-var (pop (pop top))) (DT-var top))
          (DT-app (DT-var (pop top)) (DT-var top)))))

dual-prod1 : ∀ {Δ Γ A B} -> Δ / Γ ⊢ A => B => A ∧ B
dual-prod1 = DT-lam (DT-lam (DT-prod (DT-var (pop top)) (DT-var top)))

dual-axK : ∀ {Δ Γ A B} -> Δ / Γ ⊢ □(A => B) => □ A => □ B
dual-axK = DT-lam (DT-lam (
  DT-boxE (DT-var (pop top))
          (DT-boxE (DT-var top)
                   (DT-boxI (DT-app (DT-var (pop top)) (DT-var top))))))

dual-axT :  ∀ {Δ Γ A} -> Δ / Γ ⊢ □ A => A
dual-axT = DT-lam (DT-boxE (DT-var top) (DT-modal-var top))


-- Hilbert K is contained in System K.

T-hilb-to-dual : ∀ {Γ A}

  -> ThmT Γ A
  ------------
  -> · / Γ ⊢ A

T-hilb-to-dual (T-var x) = DT-var x
T-hilb-to-dual T-k = DT-lam (DT-lam (DT-var (pop top)))
T-hilb-to-dual T-s = dual-s
T-hilb-to-dual (T-MP d d₁) = DT-app (T-hilb-to-dual d) (T-hilb-to-dual d₁)
T-hilb-to-dual (T-NEC d) = DT-boxI (T-hilb-to-dual d)
T-hilb-to-dual T-prod1 = dual-prod1
T-hilb-to-dual T-prod2 = DT-lam (DT-fst (DT-var top))
T-hilb-to-dual T-prod3 = DT-lam (DT-snd (DT-var top))
T-hilb-to-dual T-axK = dual-axK
T-hilb-to-dual T-axT = dual-axT


-- System K is contained in Hilbert K.

T-dual-to-hilb :  ∀ {Δ Γ A}

       -> Δ / Γ ⊢ A
  ------------------------
  -> ThmT (boxcx Δ ++ Γ) A

T-dual-to-hilb {Δ} {Γ} {A} (DT-var x) =
  T-var (subsetdef x (concat-subset-2 _ Γ))
T-dual-to-hilb {Δ} {Γ} (DT-modal-var x) =
  T-MP T-axT (T-var (concat-subset-1 (boxcx Δ) Γ (box∈cx x)))
T-dual-to-hilb (DT-app d d₁) = T-MP (T-dual-to-hilb d) (T-dual-to-hilb d₁)
T-dual-to-hilb (DT-lam d) = T-dedthm (T-dual-to-hilb d)
T-dual-to-hilb (DT-prod d d₁) =
  T-MP (T-MP T-prod1 (T-dual-to-hilb d)) (T-dual-to-hilb d₁)
T-dual-to-hilb (DT-fst d) = T-MP T-prod2 (T-dual-to-hilb d)
T-dual-to-hilb (DT-snd d) = T-MP T-prod3 (T-dual-to-hilb d)
T-dual-to-hilb {Δ} {Γ} {□ A}(DT-boxI d) =
  T-weak (weakmany (boxcx Δ) Γ)
         (T-normal-ded (subst (λ Δ → ThmT Δ A) (leftid++ Δ) (T-dual-to-hilb d)))
T-dual-to-hilb {Δ} {Γ} {C} (DT-boxE {A} {.C} d e) =
  let x = T-dual-to-hilb d in
  let y = T-dual-to-hilb e in
    T-cut x (T-weak (swap-out (boxcx Δ) Γ (□ A)) y)


T-dual-to-hilb-corr :  ∀ {Γ A}

  -> · / Γ ⊢ A
  ------------
  -> ThmT Γ A

T-dual-to-hilb-corr {Γ} {A} p =
  subst (λ Δ → ThmT Δ A) (leftid++ Γ) (T-dual-to-hilb p)

