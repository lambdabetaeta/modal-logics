module K4.HilbK4vsDualK4 where

open import Relation.Binary.PropositionalEquality
open import Basics
open import K4.HilbertK4
open import K4.DualK4

-----------------------------------------------------------------
-- Proof of equivalence between Hilbert K4 and dual-context K4 --
-----------------------------------------------------------------

dual-s : ∀ {Δ Γ A B C} -> Δ / Γ ⊢ (A => B => C) => (A => B) => (A => C)
dual-s =  DK4-lam (DK4-lam (DK4-lam
  (DK4-app (DK4-app (DK4-var (pop (pop top))) (DK4-var top))
          (DK4-app (DK4-var (pop top)) (DK4-var top)))))

dual-prod1 : ∀ {Δ Γ A B} -> Δ / Γ ⊢ A => B => A ∧ B
dual-prod1 = DK4-lam (DK4-lam (DK4-prod (DK4-var (pop top)) (DK4-var top)))

dual-axK : ∀ {Δ Γ A B} -> Δ / Γ ⊢ □(A => B) => □ A => □ B
dual-axK = DK4-lam (DK4-lam (
  DK4-boxE (DK4-var (pop top))
          (DK4-boxE (DK4-var top)
                   (DK4-boxI (DK4-app (DK4-var (pop top)) (DK4-var top))))))

dual-ax4 : ∀ {Δ Γ A} -> Δ / Γ ⊢ □ A => □ □ A
dual-ax4 = DK4-lam (DK4-boxE (DK4-var top) (DK4-boxI (DK4-boxI (DK4-var top))))


-- Hilbert K4 is contained in System K4.

K4-hilb-to-dual : ∀ {Γ A}

   -> ThmK4 Γ A
   ------------
   -> · / Γ ⊢ A

K4-hilb-to-dual (K4-var x) = DK4-var x
K4-hilb-to-dual K4-k = DK4-lam (DK4-lam (DK4-var (pop top)))
K4-hilb-to-dual K4-s = dual-s
K4-hilb-to-dual (K4-MP d e) = DK4-app (K4-hilb-to-dual d) (K4-hilb-to-dual e)
K4-hilb-to-dual (K4-NEC d) = DK4-boxI (K4-hilb-to-dual d)
K4-hilb-to-dual K4-prod1 = dual-prod1
K4-hilb-to-dual K4-prod2 = DK4-lam (DK4-fst (DK4-var top))
K4-hilb-to-dual K4-prod3 = DK4-lam (DK4-snd (DK4-var top))
K4-hilb-to-dual K4-axK = dual-axK
K4-hilb-to-dual K4-ax4 = dual-ax4


-- System K4 is contained in Hilbert K4.

K4-dual-to-hilb :  ∀ {Δ Γ A}

        -> Δ / Γ ⊢ A
  -------------------------
  -> ThmK4 (boxcx Δ ++ Γ) A

K4-dual-to-hilb {Δ} {Γ} {A} (DK4-var x) =
  K4-var (subsetdef x (concat-subset-2 _ Γ))
K4-dual-to-hilb (DK4-app d e) = K4-MP (K4-dual-to-hilb d) (K4-dual-to-hilb e)
K4-dual-to-hilb (DK4-lam d) = K4-dedthm (K4-dual-to-hilb d)
K4-dual-to-hilb (DK4-prod d e) =
  K4-MP (K4-MP K4-prod1 (K4-dual-to-hilb d)) (K4-dual-to-hilb e)
K4-dual-to-hilb (DK4-fst d) = K4-MP K4-prod2 (K4-dual-to-hilb d)
K4-dual-to-hilb (DK4-snd d) = K4-MP K4-prod3 (K4-dual-to-hilb d)
K4-dual-to-hilb {Δ} {Γ} {□ A} (DK4-boxI d) =
  K4-weak (weakmany (boxcx Δ) Γ)
          (K4-Four (K4-dual-to-hilb d))
K4-dual-to-hilb {Δ} {Γ} {C} (DK4-boxE {A} {.C} d e) =
  let x = K4-dual-to-hilb d in
  let y = K4-dual-to-hilb e in
    K4-cut x (K4-weak (swap-out (boxcx Δ) Γ (□ A)) y)


K4-dual-to-hilb-corr :  ∀ {Γ A}

  -> · / Γ ⊢ A
  ------------
  -> ThmK4 Γ A

K4-dual-to-hilb-corr {Γ} {A} p =
  subst (λ Δ → ThmK4 Δ A) (leftid++ Γ) (K4-dual-to-hilb p)
