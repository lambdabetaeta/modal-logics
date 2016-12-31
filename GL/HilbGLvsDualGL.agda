module GL.HilbGLvsDualGL where

open import Relation.Binary.PropositionalEquality
open import Basics
open import GL.HilbertGL
open import GL.DualGL

-- Proof of equivalence of Hilbert GL with dual-context system GL.

dual-s : ∀ {Δ Γ A B C} -> Δ / Γ ⊢ (A => B => C) => (A => B) => (A => C)
dual-s =  DGL-lam (DGL-lam (DGL-lam
  (DGL-app (DGL-app (DGL-var (pop (pop top))) (DGL-var top))
          (DGL-app (DGL-var (pop top)) (DGL-var top)))))

dual-prod1 : ∀ {Δ Γ A B} -> Δ / Γ ⊢ A => B => A ∧ B
dual-prod1 = DGL-lam (DGL-lam (DGL-prod (DGL-var (pop top)) (DGL-var top)))

dual-axK : ∀ {Δ Γ A B} -> Δ / Γ ⊢ □(A => B) => □ A => □ B
dual-axK = DGL-lam (DGL-lam
             (DGL-boxE (DGL-var (pop top))
                       (DGL-boxE (DGL-var top)
                                 (DGL-boxI (DGL-app (DGL-var (pop (pop top)))
                                                    (DGL-var (pop top)))))))

dual-ax4 : ∀ {Δ Γ A} -> Δ / Γ ⊢ □ A => □ □ A
dual-ax4 = DGL-lam (DGL-boxE (DGL-var top)
                             (DGL-boxI (DGL-boxI (DGL-var (pop top)))))

dual-axW : ∀ {Δ Γ A} -> Δ / Γ ⊢ □ (□ A => A) => □ A
dual-axW = DGL-lam (DGL-boxE (DGL-var top)
                             (DGL-boxI (DGL-app (DGL-var (pop top))
                                                (DGL-var top))))

-- Hilbert GL is contained in System GL.

GL-hilb-to-dual : ∀ {Γ A}

   -> ThmGL Γ A
   ------------
   -> · / Γ ⊢ A

GL-hilb-to-dual (GL-var x) = DGL-var x
GL-hilb-to-dual GL-k = DGL-lam (DGL-lam (DGL-var (pop top)))
GL-hilb-to-dual GL-s = dual-s
GL-hilb-to-dual (GL-MP d e) = DGL-app (GL-hilb-to-dual d) (GL-hilb-to-dual e)
GL-hilb-to-dual (GL-NEC d) = DGL-boxI (weak (GL-hilb-to-dual d) subsetempty)
GL-hilb-to-dual GL-prod1 = dual-prod1
GL-hilb-to-dual GL-prod2 = DGL-lam (DGL-fst (DGL-var top))
GL-hilb-to-dual GL-prod3 = DGL-lam (DGL-snd (DGL-var top))
GL-hilb-to-dual GL-axK = dual-axK
GL-hilb-to-dual GL-axW = dual-axW


-- System GL is contained in Hilbert GL.

GL-dual-to-hilb :  ∀ {Δ Γ A}

        -> Δ / Γ ⊢ A
  -------------------------
  -> ThmGL (boxcx Δ ++ Γ) A

GL-dual-to-hilb {Δ} {Γ} {A} (DGL-var x) =
  GL-var (subsetdef x (concat-subset-2 _ Γ))
GL-dual-to-hilb (DGL-app d e) = GL-MP (GL-dual-to-hilb d) (GL-dual-to-hilb e)
GL-dual-to-hilb (DGL-lam d) = GL-dedthm (GL-dual-to-hilb d)
GL-dual-to-hilb (DGL-prod d e) =
  GL-MP (GL-MP GL-prod1 (GL-dual-to-hilb d)) (GL-dual-to-hilb e)
GL-dual-to-hilb (DGL-fst d) = GL-MP GL-prod2 (GL-dual-to-hilb d)
GL-dual-to-hilb (DGL-snd d) = GL-MP GL-prod3 (GL-dual-to-hilb d)
GL-dual-to-hilb {Δ} {Γ} {□ A} (DGL-boxI d) =
  GL-weak (weakmany (boxcx Δ) Γ)
          (GL-lob (GL-dual-to-hilb d))
GL-dual-to-hilb {Δ} {Γ} {C} (DGL-boxE {A} {.C} d e) =
  let x = GL-dual-to-hilb d in
  let y = GL-dual-to-hilb e in
    GL-cut x (GL-weak (swap-out (boxcx Δ) Γ (□ A)) y)


GL-dual-to-hilb-corr :  ∀ {Γ A}

  -> · / Γ ⊢ A
  ------------
  -> ThmGL Γ A

GL-dual-to-hilb-corr {Γ} {A} p =
  subst (λ Δ → ThmGL Δ A) (leftid++ Γ) (GL-dual-to-hilb p)
