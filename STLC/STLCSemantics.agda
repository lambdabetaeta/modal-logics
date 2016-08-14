module STLC.STLCSemantics where

infixl 0 _⊩_

open import Basics
open import Data.Product renaming (_,_ to pair)
open import STLC.STLC

data One : Set where
  one : One


-- Neutral and normal forms.

data Ne (Γ : Cx simple) : (A : Ty simple) -> Set where

  STLC-ne-var : ∀ {A}
  
     -> A ∈ Γ
    ----------
     -> Ne Γ A

  STLC-ne-app : ∀ {A B}

    -> Ne Γ (A => B)    -> Γ ⊢ A
    -----------------------------
            -> Ne Γ B

  STLC-ne-fst : ∀ {A B}

    -> Ne Γ (A ∧ B)
    ---------------
      -> Ne Γ A

  STLC-ne-snd : ∀ {A B}

    -> Ne Γ (A ∧ B)
    ---------------
       -> Ne Γ B
       

data Nf (Γ : Cx simple) : (A : Ty simple) -> Set where

  STLC-nf-ne : ∀ {A}

    -> Ne Γ A
    -----------
    -> Nf Γ A


  STLC-nf-lam : ∀ {A B}

    -> Nf (Γ , A) B
    -----------------
    -> Nf Γ (A => B)

  STLC-nf-prod : ∀ {A B}

    ->  Nf Γ A    -> Nf Γ B
    -----------------------
       ->  Nf Γ (A ∧ B)

  STLC-nf-unit :

    ------------
      Nf Γ T


insert-ne : ∀ {Γ A} -> Ne Γ A -> Γ ⊢ A
insert-ne (STLC-ne-var p) = STLC-var p
insert-ne (STLC-ne-app p q) = STLC-app (insert-ne p) q
insert-ne (STLC-ne-fst p) = STLC-fst (insert-ne p)
insert-ne (STLC-ne-snd p) = STLC-snd (insert-ne p)

insert-nf : ∀ {Γ A} -> Nf Γ A -> Γ ⊢ A
insert-nf (STLC-nf-ne x) = insert-ne x
insert-nf (STLC-nf-lam p) = STLC-lam (insert-nf p)
insert-nf (STLC-nf-prod p q) = STLC-prod (insert-nf p) (insert-nf q)
insert-nf (STLC-nf-unit) = STLC-unit

ne-weak : ∀ {Γ Γ' A} -> Ne Γ A -> Γ ⊆ Γ' -> Ne Γ' A
ne-weak (STLC-ne-var p) q = STLC-ne-var (q p)
ne-weak (STLC-ne-app p x) q = STLC-ne-app (ne-weak p q) (STLC-weak-many x q)
ne-weak (STLC-ne-fst p) q = STLC-ne-fst (ne-weak p q)
ne-weak (STLC-ne-snd p) q = STLC-ne-snd (ne-weak p q)


-- Semantics

[[_]] : Ty simple -> Cx simple -> Set
[[ P x ]] Γ = Ne Γ (P x)
[[ A => B ]] Γ = ∀ {Γ'} -> (Γ ⊆ Γ') -> [[ A ]] Γ' -> [[ B ]] Γ'
[[ A ∧ B ]] Γ = [[ A ]] Γ × [[ B ]] Γ
[[ unit ]] Γ = One

rename : ∀ {Γ Γ' A} -> Γ ⊆ Γ' -> [[ A ]] Γ -> [[ A ]] Γ'
rename {A = P x} p m = ne-weak m p
rename {A = A => B} p x q y = x (incl-trans p q) y
rename {A = A ∧ B} p x = {!!}
rename {A = T} p x = {!!}


-- Environments.

data _⊩_ :  Cx simple -> Cx simple -> Set where
  empty : ∀ {Γ} -> Γ ⊩ ·
  cons : ∀ {Γ Θ A} -> Γ ⊩ Θ -> [[ A ]] Γ -> Γ ⊩ Θ , A

get-env : ∀ {Γ Θ A} -> Γ ⊩ Θ -> A ∈ Θ -> [[ A ]] Γ
get-env empty ()
get-env (cons E x) top = x
get-env (cons E x) (pop p) = get-env E p

env-weak : ∀ {Γ Γ' Θ} -> (Γ ⊩ Θ) -> (Γ ⊆ Γ') -> (Γ' ⊩ Θ)
env-weak empty p = empty
env-weak (cons E x) p = cons (env-weak E p) (rename p x)  


-- Semantic map.

sem : ∀ {Γ Θ A} -> Θ ⊢ A -> (E : Γ ⊩ Θ) -> [[ A ]] Γ

sem (STLC-var x) E = get-env E x
sem (STLC-app p q) E = sem p E (subsetid _) (sem q E)
sem (STLC-lam p) E q x = sem p (cons (env-weak E q) x)
sem (STLC-prod p q) E = pair (sem p E) (sem q E)
sem (STLC-fst p) E = proj₁ (sem p E)
sem (STLC-snd p) E = proj₂ (sem p E)
sem STLC-unit E = one


-- Normalisation by evaluation.

reify :  ∀ {Γ A} -> [[ A ]] Γ -> Nf Γ A
reflect : ∀ {Γ A} -> Ne Γ A -> [[ A ]] Γ

reify {A = P i}  e = STLC-nf-ne e -- STLC-nf-ne e
reify {A = A => B} e =
  STLC-nf-lam (reify (e (weakone (subsetid _)) (reflect (STLC-ne-var top))))
reify {A = A ∧ B} e =
  STLC-nf-prod (reify (proj₁ e)) (reify (proj₂ e))
reify {A = T} e = STLC-nf-unit

reflect {A = P x} m = m
reflect {A = A => B} m p x = reflect (STLC-ne-app (ne-weak m p) (insert-nf (reify x)))
reflect {A = A ∧ B} p = pair (reflect (STLC-ne-fst p)) (reflect (STLC-ne-snd p))
reflect {A = T} p = one

normalise : ∀ {A} -> · ⊢ A -> Nf · A
normalise p = reify (sem p empty)


term : ∀ {A B} -> · ⊢ (A => B) => A => B
term = STLC-lam (STLC-lam (STLC-app (STLC-var (pop top)) (STLC-var top)))

term2 :  ∀ {A B} -> · , (A => B) , A ⊢ B
term2 = STLC-app (STLC-app (STLC-weak-many term subsetempty) (STLC-var (pop top))) (STLC-var top)

term3 = normalise (STLC-lam (STLC-lam (term2 {P 1} {P 2})))
