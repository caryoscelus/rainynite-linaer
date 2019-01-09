{-- GLApp.agda - GL app flow - bindings to T.hs
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

{-# OPTIONS --without-K #-}

module GLApp where

open import Data.Unit
open import Data.Bool
open import Data.Nat
import Data.Integer as ℤ
open import Data.List

import IO.Primitive as Prim

open import Hask
import GLFW
open GLFW.Types

{-# FOREIGN GHC
  import T
  import Strokes
  import Linear.V2
  #-}

record V2 (A : Set) : Set where
  constructor v2
  field
    x y : A

{-# COMPILE GHC V2 = data V2 (V2) #-}

Coord = ℤ.ℤ
Point = V2 Coord

Triangles : Set
Triangles = List (V2 Float)

record DrawApp (App : Set) : Set where
  field
    empty : App
    render : App → Triangles
    
    frameCount : App → ℕ
    nowFrame : App → ℕ
    
    dontClearTexture : App → App
    getNeedToClearTexture : App → Bool

    mouseCallback : GLFW.MouseCallback′ {Prim.IO ⊤} App
    cursorCallback : GLFW.CursorCallback′ {Prim.IO ⊤} App
    keyCallback : GLFW.KeyCallback′ {Prim.IO ⊤} App

{-# COMPILE GHC DrawApp = data DrawApp (DrawApp) #-}

postulate
  avgC : Coord → Coord → Coord

{-# COMPILE GHC avgC = avg #-}

postulate
  everything : ∀ {App} → DrawApp App → Prim.IO ⊤
  screenToGl : (w h : Int) (x y : Double) → V2 Coord
  wh : Int
  toZoom : Int → Int → Double
  drawLine : Double → V2 Coord -> V2 Coord -> List (V2 Float)

{-# COMPILE GHC everything = \ _ -> everything #-}
{-# COMPILE GHC screenToGl = screenToGl #-}
{-# COMPILE GHC wh = wh #-}
{-# COMPILE GHC toZoom = toZoom #-}
{-# COMPILE GHC drawLine = drawLine #-}

