module K.HilbKvsDualK where

open import Relation.Binary.PropositionalEquality
open import Basics
open import K.HilbertK
open import K.DualK

-- Proof of equivalence of Hilbert K with dual-context system K.

dual-s : ∀ {Δ Γ A B C} -> Δ / Γ ⊢ (A => B => C) => (A => B) => (A => C)
dual-s =  DK-lam (DK-lam (DK-lam
  (DK-app (DK-app (DK-var (pop (pop top))) (DK-var top))
          (DK-app (DK-var (pop top)) (DK-var top)))))

dual-prod1 : ∀ {Δ Γ A B} -> Δ / Γ ⊢ A => B => A ∧ B
dual-prod1 = DK-lam (DK-lam (DK-prod1 (DK-var (pop top)) (DK-var top)))

dual-axK : ∀ {Δ Γ A B} -> Δ / Γ ⊢ □(A => B) => □ A => □ B
dual-axK = DK-lam (DK-lam (
  DK-boxE (DK-var (pop top))
          (DK-boxE (DK-var top)
                   (DK-boxI (DK-app (DK-var (pop top)) (DK-var top))))))

-- Hilbert K is contained in System K.

K-hilb-to-dual : ∀ {Γ A}
                  -> ThmK Γ A
                 --------------
                  -> · / Γ ⊢ A

K-hilb-to-dual (K-var x) = DK-var x
K-hilb-to-dual K-k = DK-lam (DK-lam (DK-var (pop top)))
K-hilb-to-dual K-s = dual-s
K-hilb-to-dual (K-MP d d₁) = DK-app (K-hilb-to-dual d) (K-hilb-to-dual d₁)
K-hilb-to-dual (K-NEC d) = DK-boxI (K-hilb-to-dual d)
K-hilb-to-dual K-prod1 = dual-prod1
K-hilb-to-dual K-prod2 = DK-lam (DK-prod2 (DK-var top))
K-hilb-to-dual K-prod3 = DK-lam (DK-prod3 (DK-var top))
K-hilb-to-dual K-axK = dual-axK

-- System K is contained in Hilbert K

K-dual-to-hilb :  ∀ {Δ Γ A}
                           -> Δ / Γ ⊢ A
                    ------------------------------
                      -> ThmK (boxcx Δ ++ Γ) A

K-dual-to-hilb {Δ} {Γ} {A} (DK-var x) = K-var (subsetdef x (concat-subset-2 _ Γ))
K-dual-to-hilb (DK-app d d₁) = K-MP (K-dual-to-hilb d) (K-dual-to-hilb d₁)
K-dual-to-hilb (DK-lam d) = K-dedthm (K-dual-to-hilb d)
K-dual-to-hilb (DK-prod1 d d₁) = K-MP (K-MP K-prod1 (K-dual-to-hilb d)) (K-dual-to-hilb d₁)
K-dual-to-hilb (DK-prod2 d) = K-MP K-prod2 (K-dual-to-hilb d)
K-dual-to-hilb (DK-prod3 d) = K-MP K-prod3 (K-dual-to-hilb d)
K-dual-to-hilb {Δ} {Γ} {□ A}(DK-boxI d) =
  K-weak (weakmany (boxcx Δ) Γ)
         (K-normal-ded (subst (λ Δ → ThmK Δ A) (leftid++ Δ) (K-dual-to-hilb d)))
K-dual-to-hilb {Δ} {Γ} {C} (DK-boxE {A} {.C} d e) =
  let x = K-dual-to-hilb d in
  let y = K-dual-to-hilb e in
    K-cut x (K-weak (swap-out (boxcx Δ) Γ (□ A)) y)


K-dual-to-hilb-corr :  ∀ {Γ A} -> · / Γ ⊢ A -> ThmK Γ A

K-dual-to-hilb-corr {Γ} {A} p = subst (λ Δ → ThmK Δ A) (leftid++ Γ) (K-dual-to-hilb p)

