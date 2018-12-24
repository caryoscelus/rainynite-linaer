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
open import Data.List
open import Data.String using (String)
open import Function
import Reflection as R

record _፦_ {ℓ} (A B : Set ℓ) : Set ℓ where
  constructor mkLens
  field
    get : A → B
    set : B → A → A

open _፦_ public

modify : ∀ {ℓ} {A B : Set ℓ} (lens : A ፦ B) (f : B → B) → A → A
modify lens f x = set lens (f (get lens x)) x

private
  _>>=_ = R.bindTC
  _>>_ : ∀ {ℓ} {A : Set ℓ} → R.TC ⊤ → R.TC A → R.TC A
  a >> b = a >>= (λ { tt → b })
  pure = R.returnTC

module _ where
  open R

  strError : String → TC ⊤
  strError msg = typeError [ strErr msg ]

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
    (function cs) ← getDefinition f-name
      where _ → typeError [ strErr "something else" ]
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
