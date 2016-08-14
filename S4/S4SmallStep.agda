module S4.S4SmallStep where

open import Basics
open import S4.DualS4

data _→β_ {Δ Γ A} : Δ / Γ ⊢ A -> Δ / Γ ⊢ A -> Set where
  beta : ∀ {A p q} -> (DS4-app {A = A} (DS4-lam p) q) →β cut · q p
  box-beta : ∀ {A p q} -> (DS4-boxE {A = A} (DS4-boxI p) q) →β cut-modal · p q

