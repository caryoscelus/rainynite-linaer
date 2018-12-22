{-- test.agda - playing with agda/haskell interop
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

module test where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Product hiding (map ; zip)

import IO.Primitive as Prim
import IO

open import Function

open import Hask
open import FCLabels
import GLFW

{-# FOREIGN GHC
  import T
  import Strokes
  import Linear.V2
  #-}

postulate
  Coord : Set
  V2 : Set → Set

{-# COMPILE GHC V2 = type V2 #-}
{-# COMPILE GHC Coord = type Coord #-}

postulate
  DrawApp : Set
  isDrawing : DrawApp ፦ Bool
  cursor : DrawApp ፦ V2 Coord
  newShape : DrawApp → DrawApp
  appendShape : DrawApp → DrawApp
  Stroke : Set
  sPoints : Stroke ፦ List (V2 Coord)
  sZoom : Stroke ፦ Int

{-# COMPILE GHC DrawApp = type DrawApp #-}
{-# COMPILE GHC isDrawing = isDrawing #-}
{-# COMPILE GHC cursor = cursor #-}
{-# COMPILE GHC newShape = newShape #-}
{-# COMPILE GHC appendShape = appendShape #-}
{-# COMPILE GHC Stroke = type Stroke #-}
{-# COMPILE GHC sPoints = sPoints #-}
{-# COMPILE GHC sZoom = sZoom #-}

Picture : Set
Picture = List Stroke

ToTriangles : Set
ToTriangles = Int → Int → List Picture → List (V2 Float)

postulate
  everything :
    ToTriangles →
    GLFW.MouseCallback′ {Prim.IO ⊤} DrawApp →
    GLFW.CursorCallback′ {Prim.IO ⊤} DrawApp →
    Prim.IO ⊤
  screenToGl : (w h : Int) (x y : Double) -> V2 Coord
  wh : Int
  toZoom : Int → Int → Double
  drawLine : Double → V2 Coord -> V2 Coord -> List (V2 Float)
  inductionOnIntAsNat : {A : Set} (z : A) (f : A → A) → Int → A

{-# COMPILE GHC everything = everything #-}
{-# COMPILE GHC screenToGl = screenToGl #-}
{-# COMPILE GHC wh = wh #-}
{-# COMPILE GHC toZoom = toZoom #-}
{-# COMPILE GHC drawLine = drawLine #-}
{-# COMPILE GHC inductionOnIntAsNat = \ _ -> inductionOnIntAsNat #-}

_⟫_ : ∀ {ℓ} {A B C : Set ℓ} (F : A → B) (G : B → C) → (A → C)
_⟫_ = flip _∘′_

when′ : ∀ {ℓ} {A : Set ℓ} (cond : Bool) → (A → A) → (A → A)
when′ false _ = id
when′ true f = f

mouseCallback : GLFW.MouseCallback DrawApp
mouseCallback button state mods =
  let
    pressed = state GLFW.== GLFW.MouseButtonState'Pressed
  in
    set isDrawing pressed ⟫ when′ pressed newShape

cursorCallback : GLFW.CursorCallback DrawApp
cursorCallback app x y =
  (set cursor (screenToGl wh wh x y) ⟫ λ app →
  let
    draw = get isDrawing app
  in
    when′ draw appendShape app) app

Int⇒ℕ : Int → ℕ
Int⇒ℕ = inductionOnIntAsNat zero suc

concat : ∀ {A} → List (List A) → List A
concat = foldr _++_ []

map : ∀ {A B} → (A → B) → List A → List B
map f = foldr (λ x ys → f x ∷ ys) []

reverse : ∀ {A} → List A → List A
reverse = foldr (λ x xs → xs ++ (x ∷ [])) []

case[]_[]→_x∷xs→_ : {A B : Set} → List A → B → (A → List A → B) → B
case[] xs []→ nil x∷xs→ cons
  with foldr (λ
    { y (inj₁ tt) → inj₂ (y , [])
    ; y (inj₂ (x , xs)) → inj₂ (y , x ∷ xs)
    })
    (inj₁ tt) xs
...  | inj₁ tt = nil
...  | inj₂ (head , tail) = cons head tail

{-# NON_TERMINATING #-}
zip : ∀ {A B} → List A → List B → List (A × B)
zip xs ys = case[] xs
  []→ []
  x∷xs→ λ x xs → case[] ys
    []→ []
    x∷xs→ λ y ys → (x , y) ∷ zip xs ys

drop : ∀ {A} → ℕ → List A → List A
drop zero xs = xs
drop (suc n) xs = case[] xs
  []→ []
  x∷xs→ λ x xs → drop n xs

pic⇒triangles : Int → Picture → List (V2 Float)
pic⇒triangles zoom = foldr addStroke []
  where
    addStroke :
      (stroke : Stroke) (vertices : List (V2 Float)) → List (V2 Float)
    addStroke stroke =
      let
        sp = get sPoints stroke
        q = toZoom zoom (get sZoom stroke)
        ss = zip sp (drop 1 sp)
      in
        concat (map (uncurry (drawLine q)) ss) ++_

{-# NON_TERMINATING #-}
getLast : ∀ {A} (z : A) (xs : List A) → A
getLast z xs = case[] xs
  []→ z
  x∷xs→ λ x xs → getLast x xs

index : ∀ {A} (z : A) (n : ℕ) (xs : List A) → A
index z zero xs = case[] xs
  []→ z
  x∷xs→ λ x xs → x
index z (suc n) xs = case[] xs
  []→ z
  x∷xs→ λ x xs → index x n xs

getAround : ∀ {A} (z : A) (n : ℕ) (xs : List A) → A × A
getAround z zero xs = getLast z xs , index z 1 xs
getAround z (suc n) xs = index z n xs , index z (suc (suc n)) xs

iStrokes : Stroke → Stroke → Stroke
iStrokes = λ _ z → z

interpolate : Int → Picture → Picture → List (V2 Float)
interpolate zoom before after =
  pic⇒triangles zoom (map (uncurry iStrokes) (zip before after))

toTriangles : ToTriangles
toTriangles zoom n′ frames =
  let
    n = Int⇒ℕ n′
  in
    pic⇒triangles zoom (index [] n frames)

{- case[] drop n frames
  []→ []
  x∷xs→ λ frame tail → case[] frame
    []→ pic⇒triangles zoom frame -- uncurry (interpolate zoom) (getAround frame n frames)
    x∷xs→ λ _ _ → pic⇒triangles zoom frame -}

main = run $ do
  lift $ everything toTriangles
    (mouseCallbackWrap mouseCallback)
    (cursorCallbackWrap cursorCallback)
  where
    open IO
    open GLFW
