{-- Util.agda - random small useful function
 -- Copyright (C) 2019 caryoscelus
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

{-# OPTIONS --safe --without-K #-}

module Util where

open import Data.Bool
open import Function

infixl 10 _⟫_

_⟫_ : ∀ {ℓ} {A B C : Set ℓ} (F : A → B) (G : B → C) → (A → C)
_⟫_ = flip _∘′_

when′ : ∀ {ℓ} {A : Set ℓ} (cond : Bool) → (A → A) → (A → A)
when′ false _ = id
when′ true f = f
