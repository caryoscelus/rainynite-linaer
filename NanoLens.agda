{-- NanoLens.agda - very basic lens with auto-derivation for records
 -- Copyright (C) 2018 caryoscelus
 --
 -- This program is free software: you can redistribute it and/or modify
 -- it under the terms of the GNU General Public License as published by
 -- the Free Software Foundation, either version 3 of the License, or
 -- (at your option) any later version.
 --
 -- This program is distributed in the hope that it will be useful,
 -- but WITHOUT ANY WARRANTY; without even the implied warranty of
 -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -- GNU General Public License for more details.
 --
 -- You should have received a copy of the GNU General Public License
 -- along with this program.  If not, see <http://www.gnu.org/licenses/>.
 --}

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Show renaming (show to ℕ-show)
open import Data.List
open import Data.Maybe using
  ( Maybe ; just ; nothing )
open import Data.String using (String)
open import Function
import Relation.Binary as Bin
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality using
  ( _≡_ ; refl )
import Reflection as R

record _፦_ {ℓ} (A B : Set ℓ) : Set ℓ where
  constructor mkLens
  field
    get : A → B
    set : B → A → A

open _፦_ public

modify : ∀ {ℓ} {A B : Set ℓ} (lens : A ፦ B) (f : B → B) → A → A
modify lens f x = set lens (f (get lens x)) x

infixl 10 _፦⟫_

_፦⟫_ : ∀ {ℓ} {A B C : Set ℓ} → A ፦ B → B ፦ C → A ፦ C
get (f ፦⟫ g) = get g ∘ get f
set (f ፦⟫ g) z x = modify f (set g z) x

private
  _>>=_ = R.bindTC
  _>>_ : ∀ {ℓ} {A : Set ℓ} → R.TC ⊤ → R.TC A → R.TC A
  a >> b = a >>= (λ { tt → b })
  pure = R.returnTC
  
  strError : ∀ {ℓ} {A : Set ℓ} → String → R.TC A
  strError msg = R.typeError [ R.strErr msg ]


find :
  ∀ {ℓ} {A : Set ℓ} {P : A → Set ℓ}
  (p : (x : A) → Dec (P x)) (xs : List A)
  → Maybe A
find p xs
  with filter p xs
...  | [] = nothing
...  | y ∷ _ = just y

find-index :
  ∀ {ℓ} {A : Set ℓ} {P : A → Set ℓ}
  (p : (x : A) → Dec (P x)) (xs : List A)
  → Maybe ℕ
find-index = find-index′ 0
  where
  find-index′ :
    ∀ {ℓ} {A : Set ℓ} {P : A → Set ℓ}
    (n : ℕ) (p : (x : A) → Dec (P x)) (xs : List A)
    → Maybe ℕ
  find-index′ n p [] = nothing
  find-index′ n p (x ∷ xs)
    with p x
  ...  | yes _ = just n
  ...  | no _ = find-index′ (suc n) p xs

-- could be a lens if we'd have a proof list is long enough
mod-at : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (f : A → A) → List A → List A
mod-at n f [] = []
mod-at zero f (x ∷ xs) = f x ∷ xs
mod-at (suc n) f (x ∷ xs) = x ∷ mod-at n f xs

module _ where
  open R

  autoLens′ :
    (skipped : ℕ)
    (names : List Name)
    (rec-name : Name)
    (con-name : Name)
    (rec-fields : List (Arg Name)) → TC ⊤
  autoLens′ _ [] _ _ [] = pure tt
  autoLens′ _ [] _ _ (_ ∷ _) = strError "not enough lens names"
  autoLens′ _ (_ ∷ _) _ _ [] = strError "not enough field names"
  autoLens′ skipped (lens-name ∷ names) rec c (arg i f-name ∷ fs) = do
    declareDef
      (arg (arg-info visible relevant) lens-name)
      (def (quote _፦_)
        ( arg (arg-info visible relevant) (def rec [])
        ∷ arg (arg-info visible relevant) unknown
        ∷ []))
    let
      l-pats : List (Arg Pattern)
      l-pats = replicate skipped
        (arg (arg-info visible relevant) (var "y"))
      r-pats : List (Arg Pattern)
      r-pats = replicate (length fs)
        (arg (arg-info visible relevant) (var "y"))
      l-vals : List (Arg Term)
      l-vals = applyDownFrom
        (λ n → arg (arg-info visible relevant)
          (var (n + length fs + 1) []))
        skipped
      r-vals : List (Arg Term)
      r-vals = applyDownFrom
        (λ n → arg (arg-info visible relevant)
          (var n []))
        (length fs)
      n-args : ℕ
      n-args = skipped + 1 + length fs
    defineFun lens-name
      [ clause [] (con (quote mkLens)
          ( arg (arg-info visible relevant) -- get
            (def f-name [])
          ∷ arg (arg-info visible relevant) -- set
            (lam visible (abs "x"
              (pat-lam
                [ clause
                  (arg (arg-info visible relevant)
                  (con c (l-pats ++ [
                      arg (arg-info visible irrelevant) (var "old")
                    ] ++ r-pats)) ∷ [])
                  -- ⇓⇓⇓
                  (con c (l-vals ++ [
                       arg (arg-info visible relevant) (var n-args [])
                    ] ++ r-vals))
                ] [])))
          ∷ []))
      ]
    autoLens′ (suc skipped) names rec c fs

  autoLens : (names : List Name) (rec : Name) → TC ⊤
  autoLens names rec = do
    (record′ c fields) ← getDefinition rec
      where other → strError "not a record"
    autoLens′ 0 names rec c fields

  module _ where
    open import Data.Product using (_×_ ; _,_)
    

    getGoodType :
      (type : Type)
      → TC ((Type → Type) × Name × List (Arg Term) × Type)
    getGoodType (pi (arg i (def rec-name rec-args)) (abs _ b)) =
      pure (id , rec-name , rec-args , b)
    getGoodType (pi (arg i x) (abs n b)) = do
      (pre-args , rec-name , rec-args , final) ← getGoodType b
      pure (pi (arg i x) ∘ abs n ∘ pre-args , rec-name , rec-args , final)
    getGoodType t = typeError $ strErr "Non-function type" ∷ termErr t ∷ []

    {-# TERMINATING #-}
    mapVars : (ℕ → ℕ) → Term → Term
    mapVarsArg : (ℕ → ℕ) → Arg Term → Arg Term

    mapVars fn (con c args) = con c (map (mapVarsArg fn) args)
    mapVars fn (def f args) = def f (map (mapVarsArg fn) args)
    mapVars fn (lam v (abs s x)) = lam v (abs s (mapVars fn x))
    mapVars fn (pat-lam cs args) = pat-lam cs (map (mapVarsArg fn) args) -- !
    mapVars fn (pi a (abs s x)) =
      pi (mapVarsArg fn a) (abs s (mapVars fn x))
    mapVars fn (sort s) = sort s
    mapVars fn (lit l) = lit l
    mapVars fn (meta m args) = meta m (map (mapVarsArg fn) args)
    mapVars fn unknown = unknown
    mapVars fn (var m args) = var (fn m) (map (mapVarsArg fn) args)
  
    mapVarsArg fn (arg i x) = arg i (mapVars fn x)

    bumpVars : ℕ → Term → Term
    bumpVars n = mapVars (_+ n)
    bumpVarsArg : ℕ → Arg Term → Arg Term
    bumpVarsArg n = mapVarsArg (_+ n)

    -- this isn't totally safe, though
    dropVars : ℕ → Term → Term
    dropVars n = mapVars (_∸ n)

    make-sett : (field-name : Name) → TC Name
    make-sett field-name = do
      type ← getType field-name
      (pre-arguments , rec-name , rec-args , final) ← getGoodType type

      record′ con-name fields ← getDefinition rec-name
        where
          d → strError "not a record definition"

      let
        n = length fields
        field-names = map (λ { (arg i x) → x}) fields

        rel-arg = arg (arg-info visible relevant)
        set-type = pre-arguments
          (pi (rel-arg (dropVars 1 final)) (abs "y"
            (pi (rel-arg (def rec-name (map (bumpVarsArg 1) rec-args))) (abs "x"
              (def rec-name (map (bumpVarsArg 2) rec-args))))))

      just k ← pure $ find-index (_≟-Name field-name) field-names
        where
          nothing → typeError $
            strErr "Field name not found" ∷ nameErr field-name ∷ []
      let
        all-args : List (Arg Term)
        all-args = mod-at k (λ { (arg i x) → arg i (var n [])}) $ zipWith
          (λ { m (arg i x) → arg i (var m [])})
          (downFrom n)
          fields
        all-pats : List (Arg Pattern)
        all-pats = map (λ { (arg i x) → arg i (var (showName x))}) fields

      set-name ← freshName "set"
      
      declareDef
        (arg (arg-info visible relevant) set-name)
        set-type
      defineFun set-name
        [ clause
          ( arg (arg-info visible relevant)
            (var "y")
          ∷ arg (arg-info visible relevant)
            (con con-name all-pats)
          ∷ [] -- ↓ ↓ ↓
          ) (con con-name all-args) ]
      pure set-name

    make-a-lens : (field-name : Name) → TC Name
    make-a-lens field-name = do
      set-name ← make-sett field-name
      lens-name ← freshName "lens"
      declareDef
        (arg (arg-info visible relevant) lens-name)
        (def (quote _፦_)
          ( arg (arg-info visible relevant) unknown
          ∷ arg (arg-info visible relevant) unknown
          ∷ []))
      defineFun lens-name
        [ clause [] (con (quote mkLens)
          ( arg (arg-info visible relevant) -- get
            (def field-name [])
          ∷ arg (arg-info visible relevant) -- set
            (def set-name [])
          ∷ []
          ))
        ]
      pure lens-name

    a-lens : (field-name : Name) (hole : Term) → TC ⊤
    a-lens field-name hole = do
      lens-name ← make-a-lens field-name
      unify hole (def lens-name [])

  macro
    sett : (field-name : Name) (hole : Term) → TC ⊤
    sett field-name hole = do
      set-name ← make-sett field-name
      unify hole (def set-name [])

    ፦[_] = a-lens


module _ where
  open import Data.Fin
  open import Data.Vec
  import Data.Vec as V

  ፦vec[_] : ∀ {ℓ} {A : Set ℓ} {size : ℕ} → Fin size → Vec A size ፦ A
  get ፦vec[ n ] xs = V.lookup n xs
  set ፦vec[ n ] x xs = xs [ n ]≔ x

  private
    just-a-vec : Vec ℕ 3
    just-a-vec = 3 V.∷ 5 V.∷ 9 V.∷ []

    just-another : Vec ℕ 3
    just-another = set ፦vec[ zero ] 13 just-a-vec

    just-ok : just-another ≡ 13 V.∷ 5 V.∷ 9 V.∷ []
    just-ok = refl

    record InnerVec (A : Set) : Set where
      field
        icount : ℕ
        ivec : Vec A icount

    open InnerVec

    something : InnerVec ℕ
    icount something = 2
    ivec something = 0 ∷ 1 ∷ []

    -- TODO: dependent
    -- something′ : InnerVec ℕ
    -- something′ = set (፦[ ivec ] ፦⟫ ፦vec[ 0 ]) 3 something

module _ where
  private
    record SingleNat : Set where
      constructor wrapNat
      field
        wrapped : ℕ
    open SingleNat

    t : SingleNat
    t = sett wrapped 30 (wrapNat 305)
    
    t′ : SingleNat
    t′ = set ፦[ wrapped ] 30 (wrapNat 305)

    t-ok : t ≡ wrapNat 30
    t-ok = refl

    t′-ok : t′ ≡ wrapNat 30
    t′-ok = refl

    record _×_ (A B : Set) : Set where
      constructor _,_
      field
        fst : A
        snd : B
    open _×_

    pts : ℕ × ℕ
    pts = 3 , 10

    pkk : ℕ × ℕ
    pkk = sett fst 12 pts

    pkk-ok : pkk ≡ (12 , 10)
    pkk-ok = refl

    pkk′ : ℕ × ℕ
    pkk′ = set ፦[ snd ] 155 pts

    pkk′-ok : pkk′ ≡ (3 , 155)
    pkk′-ok = refl

private
  record SingleNat : Set where
    constructor wrapNat
    field
      wrapped′ : ℕ

  unquoteDecl wrapped = autoLens [ wrapped ] (quote SingleNat)

  open import Relation.Binary.PropositionalEquality

  get-set : ∀ {w n} → (get wrapped ∘ set wrapped n) w ≡ n
  get-set = refl

  set-get : ∀ {w} → set wrapped (get wrapped w) w ≡ w
  set-get = refl

  set-set : ∀ {w n n′} →
    (set wrapped n ∘ set wrapped n′) w ≡ set wrapped n w
  set-set = refl

private 
  module test-Pair where
    record Pair (A B : Set) : Set where
      constructor pair
      field
        a′ : A
        b′ : B

    ℕ-Pair = Pair ℕ ℕ

    -- TODO
    -- unquoteDecl aℕ bℕ = autoLens (aℕ ∷ bℕ ∷ []) (quote ℕ-Pair)
    -- unquoteDecl a b = autoLens (a ∷ b ∷ []) (quote Pair)
