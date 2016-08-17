module STLC.HilbIPLvsSTLC where

open import Relation.Binary.PropositionalEquality
open import Basics
open import STLC.HilbertIPL
open import STLC.STLC

-- Proof of equivalence of IPL with STLC.

s : ∀ {Δ Γ A B C} -> Γ ⊢ (A => B => C) => (A => B) => (A => C)
s =  STLC-lam (STLC-lam (STLC-lam
  (STLC-app (STLC-app (STLC-var (pop (pop top))) (STLC-var top))
          (STLC-app (STLC-var (pop top)) (STLC-var top)))))

prod1 : ∀ {Δ Γ A B} -> Γ ⊢ A => B => A ∧ B
prod1 = STLC-lam (STLC-lam (STLC-prod (STLC-var (pop top)) (STLC-var top)))

-- Hilbert IPL is contained in STLC.

hilb-to-dual : ∀ {Γ A}

  -> ThmIPL Γ A
  -------------
    -> Γ ⊢ A

hilb-to-dual p = ?

{-

hilb-to-dual (var x) = STLC-var x
hilb-to-dual k = STLC-lam (STLC-lam (STLC-var (pop top)))
hilb-to-dual s = dual-s
hilb-to-dual (MP d e) = STLC-app (hilb-to-dual d) (hilb-to-dual e)
hilb-to-dual prod1 = dual-prod
hilb-to-dual prod2 = STLC-lam (STLC-fst (STLC-var top))
hilb-to-dual prod3 = STLC-lam (STLC-snd (STLC-var top))
-}


-- STLC is contained in Hilbert IPL.

dual-to-hilb :  ∀ {Γ A}

    -> Γ ⊢ A
  -------------
  -> ThmIPL Γ A

dual-to-hilb {Δ} {Γ} {A} (STLC-var x) =
  IPL-var (subsetdef x (concat-subset-2 _ Γ))
dual-to-hilb (STLC-app d d₁) = IPL-MP (dual-to-hilb d) (dual-to-hilb d₁)
dual-to-hilb (STLC-lam d) = dedthm (dual-to-hilb d)
dual-to-hilb (STLC-prod d d₁) =
  MP (MP prod1 (dual-to-hilb d)) (dual-to-hilb d₁)
dual-to-hilb (STLC-fst d) = MP prod2 (dual-to-hilb d)
dual-to-hilb (STLC-snd d) = MP prod3 (dual-to-hilb d)


dual-to-hilb-corr :  ∀ {Γ A}

  -> · / Γ ⊢ A
  ------------
  -> ThmK Γ A

dual-to-hilb-corr {Γ} {A} p =
  subst (λ Δ → ThmK Δ A) (leftid++ Γ) (dual-to-hilb p)

