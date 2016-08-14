module K.KSemantics where

infixl 0 _/_⊢_/_

open import Basics
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product renaming (_,_ to pair)
open import K.DualK

data One : Set where
  one : One

data Ne (Δ Γ : Cx modal) : (A : Ty modal) -> Set where

  DK-ne-var : ∀ {A}
                     -> (p : A ∈ Γ)
                 ------------------------
                     -> Ne Δ Γ A

  DK-ne-app : ∀ {A B}

                  -> Ne Δ Γ (A => B)   -> Δ / Γ ⊢ A
                 --------------------------------------
                        -> Ne Δ Γ B

  DK-ne-prod2 : ∀ {A B}

                 -> Ne Δ Γ (A ∧ B)
                --------------------
                   -> Ne Δ Γ A

  DK-ne-prod3 : ∀ {A B}

                 -> Ne Δ Γ (A ∧ B)
                --------------------
                   -> Ne Δ Γ B

  DK-ne-boxE : ∀ {A C}

                  -> Ne Δ Γ (□ A)    ->  (Δ , A) / Γ ⊢ C
                -----------------------------------------
                             -> Ne Δ Γ C


data Nf (Δ Γ : Cx modal) : (A : Ty modal) -> Set where


  DK-nf-ne : ∀ {A}

                     -> Ne Δ Γ A
                  ----------------------
                     -> Nf Δ Γ A


  DK-nf-lam : ∀ {A B}

                     -> Nf Δ (Γ , A) B
                 --------------------------
                     -> Nf Δ Γ (A => B)

  DK-nf-prod1 : ∀ {A B}

                  ->  Nf Δ Γ A   -> Nf Δ Γ B
                 -----------------------------
                     -> Nf Δ Γ (A ∧ B)

  DK-nf-boxI : ∀ {A}

                     -> Nf · Δ A
                 ---------------------
                     -> Nf Δ Γ (□ A)


insert-ne : ∀ {Δ Γ A} -> Ne Δ Γ A -> Δ / Γ ⊢ A
insert-ne (DK-ne-var p) = DK-var p
insert-ne (DK-ne-app p q) = DK-app (insert-ne p) q
insert-ne (DK-ne-prod2 p) = DK-prod2 (insert-ne p)
insert-ne (DK-ne-prod3 p) = DK-prod3 (insert-ne p)
insert-ne (DK-ne-boxE p q) = DK-boxE (insert-ne p) q

insert-nf : ∀ {Δ Γ A} -> Nf Δ Γ A -> Δ / Γ ⊢ A
insert-nf (DK-nf-ne x) = insert-ne x
insert-nf (DK-nf-lam p) = DK-lam (insert-nf p)
insert-nf (DK-nf-prod1 p p₁) = DK-prod1 (insert-nf p) (insert-nf p₁)
insert-nf (DK-nf-boxI p) = DK-boxI (insert-nf p)

ne-weak : ∀ {Δ Γ Γ' A} -> Ne Δ Γ A -> Γ ⊆ Γ' -> Ne Δ Γ' A
ne-weak (DK-ne-var p) q = DK-ne-var (q p)
ne-weak (DK-ne-app p x) q = DK-ne-app (ne-weak p q) (DK-weak-many x q)
ne-weak (DK-ne-prod2 p) q = DK-ne-prod2 (ne-weak p q)
ne-weak (DK-ne-prod3 p) q = DK-ne-prod3 (ne-weak p q)
ne-weak (DK-ne-boxE p x) q = DK-ne-boxE (ne-weak p q) (DK-weak-many x q)


[[_]] : Ty modal -> Cx modal -> Cx modal -> Set
[[ P x ]] Δ Γ = Ne Δ Γ (P x)
[[ A => B ]] Δ Γ = ∀ {Γ'} -> Γ ⊆ Γ' -> [[ A ]] Δ Γ' -> [[ B ]] Δ Γ'
[[ A ∧ B ]] Δ Γ = [[ A ]] Δ Γ × [[ B ]] Δ Γ
[[ □ A ]] Δ Γ = [[ A ]] · Δ

rename : ∀ {Δ Γ Γ'} -> (A : Ty modal) -> Γ ⊆ Γ' -> [[ A ]] Δ Γ -> [[ A ]] Δ Γ'
rename (P i) p x = ne-weak x p
rename (A => B) p x q z = x (incl-trans p q) z
rename (A ∧ B) p x = pair (rename A p (proj₁ x)) (rename B p (proj₂ x))
rename (□ A) p x = x

data _/_⊢_/_ :  Cx modal -> Cx modal -> Cx modal -> Cx modal -> Set where
  empty : ∀ {Δ Γ} -> Δ / Γ ⊢ · / ·
  right : ∀ {Δ Γ Η Θ A} -> (Δ / Γ ⊢ Η / Θ) -> [[ A ]] Δ Γ -> (Δ / Γ ⊢ Η / Θ , A)
  left : ∀ {Δ Γ Η Θ A} -> (Δ / Γ ⊢ Η / Θ) -> [[ A ]] · Δ -> (Δ / Γ ⊢ Η , A / Θ)

get-env : ∀ {Δ Γ Θ Η A} -> Δ / Γ ⊢ Θ / Η -> A ∈ Η -> [[ A ]] Δ Γ

get-env (right E x) top = x
get-env (left E x) top = get-env E top
get-env (right E x) (pop p) = get-env E p
get-env (left E x) (pop p) = get-env E (pop p)

keep-only-modal : ∀ {Δ Γ Η Θ} -> (Δ / Γ ⊢ Η / Θ) ->  (· / Δ ⊢ · / Η)
keep-only-modal empty = empty
keep-only-modal (right E x) = keep-only-modal E
keep-only-modal (left E x) = right (keep-only-modal E) x

env-weak : ∀ {Δ Γ Γ' Η Θ} -> (Δ / Γ ⊢ Η / Θ) -> (Γ ⊆ Γ') -> (Δ / Γ' ⊢ Η / Θ)
env-weak empty p = empty
env-weak (right E x) p = right (env-weak E p) (rename _ p x)
env-weak (left E x) p = left (env-weak E p) x

id-ctxt : ∀ {Δ Γ} -> Δ / Γ ⊢ Δ / Γ
id-ctxt {Δ} {Γ} = {!!} 

sem : ∀ {Δ Γ Θ Η A} -> Θ / Η ⊢ A -> (E : Δ / Γ ⊢ Θ / Η) -> [[ A ]] Δ Γ
sem (DK-var x) E = get-env E x
sem (DK-app p q) E = sem p E (subsetid _) (sem q E)
sem (DK-lam p) E q x = sem p (right (env-weak E q) x)
sem (DK-prod1 p q) E = pair (sem p E) (sem q E)
sem (DK-prod2 p) E = proj₁ (sem p E)
sem (DK-prod3 p) E = proj₂ (sem p E)
sem (DK-boxI p) E = {!!}
sem (DK-boxE p q) E = {!!} -- sem q (left E (sem p E))

reify :  ∀ {Δ Γ A} -> [[ A ]] Δ Γ -> Nf Δ Γ A
reflect : ∀ {Δ Γ A} -> Ne Δ Γ A -> [[ A ]] Δ Γ

reify {A = P x} e = DK-nf-ne e
reify {Δ} {Γ} {A = A => B} e =
  DK-nf-lam (reify (e (weakone (subsetid _)) (reflect {Δ} {Γ , A} {A} (DK-ne-var top))))
reify {A = A ∧ B} e = DK-nf-prod1 (reify (proj₁ e)) (reify (proj₂ e))
reify {A = □ A} e = DK-nf-boxI (reify e)

reflect {A = P x} p = p
reflect {A = A => B} p x y = reflect (DK-ne-app (ne-weak p x) (insert-nf (reify y)))
reflect {A = A ∧ B} p = pair (reflect (DK-ne-prod2 p)) (reflect (DK-ne-prod3 p))
reflect {A = □ A} p = reflect (DK-ne-boxE p {!!})
