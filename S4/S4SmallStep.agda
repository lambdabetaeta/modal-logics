module S4.S4SmallStep where

open import Basics
open import S4.DualS4 as S4
open import STLC.STLC as STLC renaming (cut to λcut)
open import STLC.STLCSmallStep renaming (_→β_ to _→λβ_)

data _→β_ {Δ Γ} : ∀ {A} -> Δ / Γ ⊢ A -> Δ / Γ ⊢ A -> Set where

  -- Beta rules.

  beta : ∀ {A B} {p : Δ / Γ , A ⊢ B} {q : Δ / Γ ⊢ A}
  
    -> (DS4-app {A = A} (DS4-lam p) q) →β (cut · q p)
  
  box-beta : ∀ {A C} {p : Δ / · ⊢ A} {q : Δ , A / Γ ⊢ C}
  
    -> (DS4-boxE (DS4-boxI p) q) →β (cut-modal · p q)

  -- Congruence rules.
  
  cong-app-1 : ∀ {A B} {p p' : Δ / Γ ⊢ A => B} {q : Δ / Γ ⊢ A}
  
               ->  p →β p'
    ----------------------------------
    -> (DS4-app p q) →β (DS4-app p' q)

  cong-app-2 : ∀  {A B} {p : Δ / Γ ⊢ A => B} {q q' : Δ / Γ ⊢ A}
  
               ->  q →β q'
    ----------------------------------
    -> (DS4-app p q) →β (DS4-app p q')

  cong-lam : ∀ {A B} {p p' : Δ / Γ , A ⊢ B}
  
               ->  p →β p'
      ------------------------------
      -> (DS4-lam p) →β (DS4-lam p')

  cong-boxI : ∀ {A} {p p' : Δ / · ⊢ A}
  
               ->  p →β p'
     --------------------------------
     -> (DS4-boxI p) →β (DS4-boxI p')

  cong-boxE-1 : ∀ {A C} {p p' : Δ / Γ ⊢ □ A} {q : Δ , A / Γ ⊢ C}
  
               ->  p →β p'
   ------------------------------------
   -> (DS4-boxE p q) →β (DS4-boxE p' q)

  cong-boxE-2 : ∀ {A C} {p : Δ / Γ ⊢ □ A} {q q' : Δ , A / Γ ⊢ C}
  
               ->  q →β q'
   ------------------------------------
   -> (DS4-boxE p q) →β (DS4-boxE p q')


trans : ∀ {Δ Γ A} -> Δ / Γ ⊢ A -> trans-cx Δ ++ trans-cx Γ ⊢ trans-ty A

trans {Γ = Γ} (DS4-var x) = STLC-var (concat-subset-2 _ _ (∈-trans-cx x))
trans {Δ} {Γ} {A} (DS4-modal-var x) =
  STLC-var (concat-subset-1 (trans-cx Δ) (trans-cx Γ) (∈-trans-cx x))
trans (DS4-app p q) = STLC-app (trans p) (trans q)
trans (DS4-lam p) = STLC-lam (trans p)
trans (DS4-prod p q) = STLC-prod (trans p) (trans q)
trans (DS4-fst p) = STLC-fst (trans p)
trans (DS4-snd p) = STLC-snd (trans p)
trans {Δ} {Γ} {□ A} (DS4-boxI p) =
  STLC.weak (trans p) (concat-subset-1 (trans-cx Δ) (trans-cx Γ))
trans {Δ} {Γ} {C} (DS4-boxE p q) =
 let a = trans p in
 let b = STLC.weak (trans q) (swap-out (trans-cx Δ) (trans-cx Γ) _) in
   λcut · a b

emulate : ∀ {Δ Γ A} {p p' : Δ / Γ ⊢ A} -> p →β p' -> trans p →λβ trans p'
emulate beta = {!!}
emulate box-beta = {!!}
emulate (cong-app-1 q) = cong-app-1 (emulate q)
emulate (cong-app-2 q) = cong-app-2 (emulate q)
emulate (cong-lam q) = cong-lam (emulate q)
emulate (cong-boxI q) = {!!}
emulate (cong-boxE-1 q) = {!!}
emulate (cong-boxE-2 q) = {!!}

-- need lemmata:
-- p -> p implies weak p -> weak p'
-- p -> p implies lcut p q -> lcut p' q
-- (lx. trans p) (trans q) -> trans (q[p/x])
-- lcut (trans p) (trans q) -> trans (cut-modal p q)
