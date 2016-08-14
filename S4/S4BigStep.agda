module S4.S4BigStep where

open import Agda.Builtin.Unit public using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to pair)
open import Basics
open import S4.DualS4
import STLC.STLC as STLC

-- Big Step Normalisation

get-right-val : ∀ {Δ Γ Η Θ A} -> (A ∈ Θ) -> (Δ / Γ ⊢ Η / Θ) -> Val Δ Γ A
get-right-val () empty
get-right-val top (right p x) = x
get-right-val (pop q) (right p x) = get-right-val q p
get-right-val q (left p x) = get-right-val q p

-- E ⊢ M ⇓ v is to be read as "in environment E, M evaluates to whnf (val) v."

mutual

  data _⊢_⇓_ : ∀ {Η Θ Δ Γ A} -> (Δ / Γ ⊢ Η / Θ) -> (Η / Θ ⊢ A) -> (Val Δ Γ A) -> Set where


    whnf-var : ∀ {Δ Γ Η Θ A} {E : Δ / Γ ⊢ Η / Θ}
                                   -> (p : A ∈ Θ)
                   ------------------------------------------
                      ->  E ⊢ (DS4-var p) ⇓ (get-right-val p E)


    whnf-lam : ∀ {Δ Γ Η Θ A B} {m : Η / Θ , A ⊢ B}  {E : Δ / Γ ⊢ Η / Θ}

                   -----------------------------------------------------
                      ->  E ⊢ (DS4-lam  m) ⇓ (DS4-val-lam E m)

    whnf-app : ∀ {Η Θ Δ Γ E A B} {m : Η / Θ ⊢ A => B} {n : Η / Θ ⊢ A}
                                 {f : Val Δ Γ (A => B)} {x : Val Δ Γ A} {v}

                     -> E ⊢ m ⇓ f    -> E ⊢ n ⇓ x     -> f $ x >> v
                   ------------------------------------------------------
                                -> E ⊢ (DS4-app m n) ⇓ v

    whnf-boxI : ∀ {Δ Γ Η Θ A} {m : Η / · ⊢ A} {E : Δ / Γ ⊢ Η / Θ}

                   ---------------------------------------------
                     -> E ⊢ (DS4-boxI m) ⇓ (DS4-val-boxI E m)

    whnf-boxE : ∀ {Η Θ Δ Γ E A C} {m : Η / Θ ⊢ □ A}   {n : Η , A / Θ ⊢ C}
                                  {g : Val Δ Γ (□ A)} {v : Val (Δ , A) Γ C}
                                  {w : Val Δ Γ C}

                                  -> E ⊢ m ⇓ g
                     -> (ctxt-insert-left _ _ _ _ E) ⊢ n ⇓ v
                                  -> g % v >> w
                   --------------------------------------------
                           -> E ⊢ (DS4-boxE m n) ⇓ w


    whnf-prod1 : ∀ {Δ Γ Η Θ A B}  {E : Δ / Γ ⊢ Η / Θ}
                   {m : Η / Θ ⊢ A} {n : Η / Θ ⊢ B}

                   -----------------------------------------------
                    -> E ⊢ (DS4-prod1 m n) ⇓ (DS4-val-prod1 E m n)

    whnf-prod2 : ∀ {Δ Γ Η Θ A B} {m : Η / Θ ⊢ A ∧ B} {E : Δ / Γ ⊢ Η / Θ} {v w}

                     ->  E ⊢ m ⇓ v      -> fst v >> w
                   -----------------------------------
                     -> E ⊢ (DS4-prod2 m) ⇓ w


    whnf-prod3 : ∀ {Δ Γ Η Θ A B} {m : Η / Θ ⊢ A ∧ B} {E : Δ / Γ ⊢ Η / Θ} {v w}

                      -> E ⊢ m ⇓ v      -> snd v >> w     
                   ------------------------------------
                        -> E ⊢ (DS4-prod3 m) ⇓ w


  -- Dealing with arrow elimination.
  
  data _$_>>_ {Δ Γ A B} :  Val Δ Γ (A => B) -> Val Δ Γ A -> Val Δ Γ B -> Set where

    eval-app-ne : ∀ {m v} ->  DS4-val-ne m $ v >> (DS4-val-ne (DS4-ne-app m v))

    eval-app-lam : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ} {m v w} -> (right E v) ⊢ m ⇓ w -> (DS4-val-lam E m) $ v >> w


  _$_ : ∀ {Δ Γ A B v} -> (f : Val Δ Γ (A => B)) -> (x : Val Δ Γ A) -> (f $ x >> v) -> Σ (Val Δ Γ B) (λ w -> w ≡ v)

  (DS4-val-ne m $ v) eval-app-ne = pair (DS4-val-ne (DS4-ne-app m v)) refl
  (DS4-val-lam E t $ v) (eval-app-lam p) = pair _ refl

  -- Dealing with first projection.
  
  data fst_>>_ {Δ Γ A B} :  Val Δ Γ (A ∧ B) -> Val Δ Γ A -> Set where

    eval-fst-ne : ∀ {x} -> fst (DS4-val-ne x) >> (DS4-val-ne (DS4-ne-prod2 x))
    eval-fst-prod1 : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ} {a b v} -> E ⊢ a ⇓ v -> fst (DS4-val-prod1 E a b) >> v

  fst-val-str : ∀ {Δ Γ A B v} -> (x : Val Δ Γ (A ∧ B)) -> (p : fst x >> v) -> Σ (Val Δ Γ A) (λ w -> w ≡ v)

  fst-val-str (DS4-val-ne x) eval-fst-ne = pair (DS4-val-ne (DS4-ne-prod2 x)) refl
  fst-val-str (DS4-val-prod1 E m n) (eval-fst-prod1 p) = eval-str E m p

  -- Dealing with second projection.

  data snd_>>_ {Δ Γ A B} : Val Δ Γ (A ∧ B) -> Val Δ Γ B -> Set where

    eval-snd-ne : ∀ {x} -> snd (DS4-val-ne x) >> (DS4-val-ne (DS4-ne-prod3 x))
    eval-snd-prod1 : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ} {a b v} -> E ⊢ b ⇓ v -> snd (DS4-val-prod1 E a b) >> v

  snd-val-str : ∀ {Δ Γ A B v} -> (x : Val Δ Γ (A ∧ B)) -> (p : snd x >> v) -> Σ (Val Δ Γ B) (λ w -> w ≡ v)
  snd-val-str (DS4-val-ne x) eval-snd-ne = pair (DS4-val-ne (DS4-ne-prod3 x)) refl
  snd-val-str (DS4-val-prod1 E m n) (eval-snd-prod1 p) = eval-str E n p

  -- Dealing with box-elimination.

  data _%_>>_ {Δ Γ A C} : Val Δ Γ (□ A) -> Val (Δ , A) Γ C -> Val Δ Γ C -> Set where
    eval-box-ne : ∀ {m v} ->  DS4-val-ne m % v >> (DS4-val-ne (DS4-ne-boxE m v))

    eval-box-box : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ}
                           {m : Η / · ⊢ A}  {v : Val (Δ , A) Γ C}
                           {v' : Val Δ · A} {w : Val Δ Γ C}
                              -> (ctxt-to-modal-ctxt E) ⊢ m ⇓ v'
                              -> left (id-ctxt _ _) v' ⊢ (insert-val v) ⇓ w
                              -> (DS4-val-boxI E m) % v >> w

  insert-val : ∀ {Δ Γ A} -> Val Δ Γ A -> Δ / Γ ⊢ A
  insert-val (DS4-val-ne x) = {!!}
  insert-val (DS4-val-lam E t) = {!!}
  insert-val (DS4-val-prod1 E t u) = {!!}
  insert-val (DS4-val-boxI E t) = {!!}

  _%_ : ∀ {Δ Γ A C w} -> (g : Val Δ Γ (□ A)) -> (v : Val (Δ , A) Γ C) -> (g % v >> w) -> Σ (Val Δ Γ C) (λ w' -> w' ≡ w)
  (DS4-val-ne n % v) p = pair _ refl
  (DS4-val-boxI E m % v) p = pair _ refl

  -- Evaluating to whnf.

  eval-str : ∀ {Δ Γ Η Θ A v} -> (E : Δ / Γ ⊢ Η / Θ)
         -> (t : Η / Θ ⊢ A) ->  E ⊢ t ⇓ v -> Σ (Val Δ Γ A) (λ w -> w ≡ v)

  eval-str E (DS4-var p) (whnf-var .p) = pair (get-right-val p E) refl
  eval-str E (DS4-app t u) (whnf-app p q r) with (eval-str E t p) | (eval-str E u q)
  eval-str E (DS4-app t u) (whnf-app p q r)     | pair f refl | pair x refl = (f $ x) r
  eval-str E (DS4-lam m) whnf-lam = pair (DS4-val-lam E m) refl
  eval-str E (DS4-prod1 m n) whnf-prod1 = pair (DS4-val-prod1 E m n) refl
  eval-str E (DS4-prod2 t) (whnf-prod2 p x) with (eval-str E t p)
  eval-str E (DS4-prod2 t) (whnf-prod2 p x)    | pair v refl = fst-val-str v x
  eval-str E (DS4-prod3 t) (whnf-prod3 p x) with (eval-str E t p)
  eval-str E (DS4-prod3 t) (whnf-prod3 p x)    | pair v refl = snd-val-str v x
  eval-str E (DS4-boxI m) whnf-boxI = pair (DS4-val-boxI E m) refl
  eval-str E (DS4-boxE t u) (whnf-boxE p q r)
    with (eval-str E t p) | (eval-str (ctxt-insert-left _ _ _ _ E) u q)
  ...  | pair g refl | pair v refl = (g % v) r

  -- v ↓ w is to be read "whnf v evaluates to nf w"

  boxvar : ∀ {Δ Γ A} -> Val (Δ , A) Γ (□ A)
  boxvar = DS4-val-boxI (left empty (DS4-val-ne (DS4-ne-var top))) (DS4-var top)

  data _↓_  {Δ Γ} : ∀ {A} -> (Val Δ Γ A) -> (Nf Δ Γ A) -> Set where

    nf-ne : ∀ {A v} {m : Ne Δ Γ Val A}
                              -> m ↓ne v
               -------------------------------------
                  -> (DS4-val-ne m) ↓ (DS4-nf-ne v)

    nf-lam : ∀ {A B v w} {f : Val Δ Γ (A => B)}
    
               -> (val-weak-many-right f (weakone (subsetid _))) $ (DS4-val-ne (DS4-ne-var top)) >> v   -> v ↓ w
               -------------------------------------------------------------------
                                -> f ↓ (DS4-nf-lam w)

    nf-prod1 : ∀ {A B v' w'}
                 {m : Val Δ Γ (A ∧ B)}
                 {v : Val Δ Γ A} {w : Val Δ Γ B}
    
                -> fst m >> v   -> snd m >> w   -> v ↓ v'   -> w ↓ w'
               -------------------------------------------------------
                            -> m ↓ (DS4-nf-prod1 v' w')


    nf-box : ∀ {Η Θ} {E : Δ / Γ ⊢ Η / Θ} {A}
               {m : · / Η ⊢ A} {v : Val · Δ A} {w : Nf · Δ A}
    
                 ->  (ctxt-to-modal-ctxt E) ⊢ m ⇓ v       -> v ↓ w
               -------------------------------------------------------------------
                     -> (DS4-val-boxI E m) ↓ (DS4-nf-boxI w) 


  data _↓ne_  {Δ Γ} : ∀ {A} -> (Ne Δ Γ Val A) -> (Ne Δ Γ Nf A) -> Set where
  
      nf-var : ∀ {A} {x : A ∈ Γ}
      
               -------------------------------------
                  -> (DS4-ne-var x) ↓ne (DS4-ne-var x)

      nf-app : ∀ {A B} {t : Ne Δ Γ Val (A => B)}
                       {v : Ne Δ Γ Nf (A => B)}
                       {u : Val Δ Γ A}
                       {w : Nf Δ Γ A}
      
                  -> t ↓ne v              -> u ↓ w
               -------------------------------------------
                  -> (DS4-ne-app t u) ↓ne (DS4-ne-app v w)
                  
      nf-prod2 : ∀ {A B} {t : Ne Δ Γ Val (A ∧ B)}
                         {v : Ne Δ Γ Nf (A ∧ B)}
      
                                -> t ↓ne v
               -------------------------------------------
                  -> (DS4-ne-prod2 t) ↓ne (DS4-ne-prod2 v)

      nf-prod3 : ∀ {A B} {t : Ne Δ Γ Val (A ∧ B)}
                         {v : Ne Δ Γ Nf (A ∧ B)}
      
                                -> t ↓ne v
               -------------------------------------------
                  -> (DS4-ne-prod3 t) ↓ne (DS4-ne-prod3 v)

      nf-boxE : ∀ {A C} {t : Ne Δ Γ Val (□ A)}
                        {v : Ne Δ Γ Nf (□ A)}
                        {u : Val (Δ , A) Γ C}
                        {w : Nf (Δ , A) Γ C}
      
                  -> t ↓ne v              -> u ↓ w
               -------------------------------------------
                  -> (DS4-ne-boxE t u) ↓ne (DS4-ne-boxE v w)


  quote-str : ∀ {Δ Γ A w} -> (v : Val Δ Γ A) -> v ↓ w -> Σ (Nf Δ Γ A) (λ w' -> w ≡ w')

  quote-str (DS4-val-ne x) (nf-ne y) = pair (DS4-nf-ne _) refl
  quote-str (DS4-val-ne x) (nf-lam p q) = pair (DS4-nf-lam _) refl
  quote-str (DS4-val-ne x) (nf-prod1 p q r s) = pair (DS4-nf-prod1 _ _) refl
  quote-str (DS4-val-lam E t) (nf-lam p q) = pair (DS4-nf-lam _) refl
  quote-str (DS4-val-prod1 E t u) (nf-prod1 p q r s) = pair (DS4-nf-prod1 _ _) refl
  quote-str (DS4-val-boxI E t) (nf-box p q) = pair (DS4-nf-boxI _) refl 

  quote-ne-str : ∀ {Δ Γ A w} -> (v : Ne Δ Γ Val A)
                 -> v ↓ne w -> Σ (Ne Δ Γ Nf A) (λ w' -> w ≡ w')

  quote-ne-str (DS4-ne-var x) nf-var = pair (DS4-ne-var x) refl
  quote-ne-str (DS4-ne-app t u) (nf-app p x) = pair (DS4-ne-app _ _) refl
  quote-ne-str (DS4-ne-prod2 t) (nf-prod2 p) = pair (DS4-ne-prod2 _) refl
  quote-ne-str (DS4-ne-prod3 t) (nf-prod3 p) = pair (DS4-ne-prod3 _) refl
  quote-ne-str (DS4-ne-boxE t u) (nf-boxE p x) = pair (DS4-ne-boxE _ _) refl


nf-to-val : ∀ {Δ Γ A} -> (Nf Δ Γ A) -> (Val Δ Γ A)
nf-to-term : ∀ {Δ Γ A} -> (Nf Δ Γ A) -> (Δ / Γ ⊢ A)
ne-nf-to-val-nf : ∀ {Δ Γ A} -> (Ne Δ Γ Nf A) -> (Ne Δ Γ Val A)
ne-nf-to-term :  ∀ {Δ Γ A} -> (Ne Δ Γ Nf A) -> (Δ / Γ ⊢ A)

nf-to-val (DS4-nf-ne x) = DS4-val-ne (ne-nf-to-val-nf x)
nf-to-val (DS4-nf-lam t) = DS4-val-lam (id-ctxt _ _) (nf-to-term t)
nf-to-val (DS4-nf-prod1 t u) = DS4-val-prod1 (id-ctxt _ _) (nf-to-term t) (nf-to-term u)
nf-to-val (DS4-nf-boxI t) = DS4-val-boxI (id-ctxt _ _) (nf-to-term t)

nf-to-term (DS4-nf-ne p) = ne-nf-to-term p
nf-to-term (DS4-nf-lam t) = DS4-lam (nf-to-term t)
nf-to-term (DS4-nf-prod1 t u) = DS4-prod1 (nf-to-term t) (nf-to-term u)
nf-to-term (DS4-nf-boxI t) = DS4-boxI (nf-to-term t)

ne-nf-to-val-nf (DS4-ne-var p) = DS4-ne-var p
ne-nf-to-val-nf (DS4-ne-app t u) = DS4-ne-app (ne-nf-to-val-nf t) (nf-to-val u)
ne-nf-to-val-nf (DS4-ne-prod2 t) = DS4-ne-prod2 (ne-nf-to-val-nf t)
ne-nf-to-val-nf (DS4-ne-prod3 t) = DS4-ne-prod3 (ne-nf-to-val-nf t)
ne-nf-to-val-nf (DS4-ne-boxE t u) = DS4-ne-boxE (ne-nf-to-val-nf t) (nf-to-val u)

ne-nf-to-term (DS4-ne-var p) = DS4-var p
ne-nf-to-term (DS4-ne-app t u) = DS4-app (ne-nf-to-term t) (nf-to-term u)
ne-nf-to-term (DS4-ne-prod2 t) = DS4-prod2 (ne-nf-to-term t)
ne-nf-to-term (DS4-ne-prod3 t) = DS4-prod3 (ne-nf-to-term t)
ne-nf-to-term (DS4-ne-boxE t u) = DS4-boxE (ne-nf-to-term t) (nf-to-term u)

-- Translation to STLC

trans-K : ∀ {Δ Γ A} -> Δ / Γ ⊢ A -> trans-cx (boxcx Δ) ++ trans-cx Γ STLC.⊢ trans-ty A

trans-K (DS4-var p) = STLC.STLC-var (subsetdef (∈-trans-cx p) (concat-subset-2 _ _))
trans-K (DS4-app t u) = STLC.STLC-app (trans-K t) (trans-K u)
trans-K (DS4-lam t) = STLC.STLC-lam (trans-K t)
trans-K (DS4-prod1 t u) = STLC.STLC-prod1 (trans-K t) (trans-K u)
trans-K (DS4-prod2 t) = STLC.STLC-prod2 (trans-K t)
trans-K (DS4-prod3 t) = STLC.STLC-prod3 (trans-K t)
trans-K {Δ} {Γ} {□ A} (DS4-boxI t) =
  let u = trans-K t in
    STLC.STLC-unitize (trans-cx Γ) (STLC.STLC-lam (STLC.STLC-weak-many u
    (weakone ((subst (λ x → x ⊆ trans-cx Δ ++ trans-cx Γ) (sym (leftid++ (trans-cx Δ))) (concat-subset-1 (trans-cx Δ) (trans-cx Γ)))))))
trans-K {Δ} {Γ} {_} (DS4-boxE t u) =
  STLC.STLC-cut · (trans-K t) (let p = trans-K u in STLC.STLC-weak-many p (swap-out (trans-cx (boxcx Δ)) (trans-cx Γ) _))


