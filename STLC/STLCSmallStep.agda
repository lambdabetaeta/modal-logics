module STLC.STLCSmallStep where

open import Basics
open import STLC.STLC

data _→β_ {Γ} : ∀ {A} -> Γ ⊢ A -> Γ ⊢ A -> Set where

  -- Beta rules.

  beta : ∀ {A B} {p : Γ , A ⊢ B} {q :  Γ ⊢ A}
  
    -> (STLC-app {A = A} (STLC-lam p) q) →β (cut · q p)

  -- Congruence rules.
  
  cong-app-1 : ∀ {A B} {p p' : Γ ⊢ A => B} {q : Γ ⊢ A}
  
               ->  p →β p'
    ---------------------------------
    -> (STLC-app p q) →β (STLC-app p' q)

  cong-app-2 : ∀ {A B} {p : Γ ⊢ A => B} {q q' : Γ ⊢ A}
  
               ->  q →β q'
    ---------------------------------
    -> (STLC-app p q) →β (STLC-app p q')

  cong-lam : ∀ {A B} {p p' :  Γ , A ⊢ B}
  
             ->  p →β p'
    ------------------------------
    -> (STLC-lam p) →β (STLC-lam p')
