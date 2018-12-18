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

{-# COMPILE GHC DrawApp = type DrawApp #-}
{-# COMPILE GHC isDrawing = isDrawing #-}
{-# COMPILE GHC cursor = cursor #-}
{-# COMPILE GHC newShape = newShape #-}
{-# COMPILE GHC appendShape = appendShape #-}


postulate
  everything :
    GLFW.MouseCallback′ {Prim.IO ⊤} DrawApp →
    GLFW.CursorCallback′ {Prim.IO ⊤} DrawApp →
    Prim.IO ⊤
  screenToGl : (w h : Int) (x y : Double) -> V2 Coord
  wh : Int

{-# COMPILE GHC everything = everything #-}
{-# COMPILE GHC screenToGl = screenToGl #-}
{-# COMPILE GHC wh = wh #-}

_⟫_ : ∀ {ℓ} {A B C : Set ℓ} (F : A → B) (G : B → C) → (A → C)
_⟫_ = flip _∘′_

when′ : ∀ {ℓ} {A : Set ℓ} (cond : Bool) → (A → A) → (A → A)
when′ false _ = id
when′ true f = f

mouseCallback : GLFW.MouseCallback DrawApp
mouseCallback app button state mods =
  let
    pressed = state GLFW.== GLFW.MouseButtonState'Pressed
  in
    (set isDrawing pressed ⟫ when′ pressed newShape) app

cursorCallback : GLFW.CursorCallback DrawApp
cursorCallback app x y =
  (set cursor (screenToGl wh wh x y) ⟫ λ app →
  let
    draw = get isDrawing app
  in
    when′ draw appendShape app) app

main = run $ do
  lift $ everything
    (GLFW.mouseCallbackWrap mouseCallback)
    (GLFW.cursorCallbackWrap cursorCallback)
  where
    open IO
