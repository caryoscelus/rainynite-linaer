{-- colors.agda - color app
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

module colors where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
import Data.Integer as ℤ
open import Data.List
import Data.List as L

-- import IO.Primitive as Prim
import IO

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Hask
open import Util
open import NanoLens
open import GLApp
import GLFW
open GLFW.Types

record HSV (C : Set) : Set where
  constructor hsv
  field
    hue saturation value : C

open HSV

record RGB (C : Set) : Set where
  constructor rgb
  field
    red green blue : C

open RGB

record Fin256 : Set where
  constructor fin
  field
    n : ℕ
    ok : n <′ 256

fin0 = fin 0 (≤⇒≤′ (s≤s z≤n))
finMax = fin 255 ≤′-refl

hsvRed : HSV Fin256
hue hsvRed = fin0
saturation hsvRed = finMax
value hsvRed = finMax

record ColorsApp : Set where
  field
    hsvColor : HSV Fin256 -- bah
    cursor : Point
    updated : Bool

open ColorsApp

emptyApp : ColorsApp
emptyApp = record
  { hsvColor = hsvRed
  ; cursor = v2 (ℤ.+ 0) (ℤ.+ 0)
  ; updated = true
  }

hueToRgb : Fin256 → RGB Fin256
hueToRgb x = rgb finMax fin0 fin0 -- TODO

[_/_] = ratioToFloat

rgb256⇒float : RGB Fin256 → V3 Float
rgb256⇒float c = v3
  [ Fin256.n (red c) / 256 ]
  [ Fin256.n (green c) / 256 ]
  [ Fin256.n (blue c) / 256 ]

render : ColorsApp → Triangles
render app =
  let
    col = hueToRgb ∘ hue ∘ hsvColor $ app
    black : RGB Fin256
    black = rgb fin0 fin0 fin0
    white : RGB Fin256
    white = rgb finMax finMax finMax
    ↖ = (v2 [ 0 / 1 ] [ 0 / 1 ] , black)
    ↗ = (v2 [ 1 / 1 ] [ 0 / 1 ] , black)
    ↙ = (v2 [ 0 / 1 ] [ 1 / 1 ] , col)
    ↘ = (v2 [ 1 / 1 ] [ 1 / 1 ] , white)
  in
    L.map (λ { ( xy , color ) → rgbPoint xy (rgb256⇒float color)})
      (↖ ∷ ↗ ∷ ↙ ∷ ↗ ∷ ↙ ∷ ↘ ∷ [])

ℕ⇒256 : ℕ → Fin256
ℕ⇒256 x with x <? 256
...        | yes p = fin x (≤⇒≤′ p)
...        | no _  = fin 255 ≤′-refl

Coord⇒256 : Coord → Fin256
Coord⇒256 = ℕ⇒256 ∘ λ { (ℤ.+_ n) → n ; (ℤ.-[1+_] n) → 0 }

mouseCallback : GLFW.MouseCallback ColorsApp
mouseCallback button MouseButtonState'Pressed _ app =
  ( set ፦[ updated ] true
  ⟫ set (፦[ hsvColor ] ፦⟫ ፦[ saturation ]) (Coord⇒256 ∘ V2.x ∘ cursor $ app)
  ⟫ set (፦[ hsvColor ] ፦⟫ ፦[ value ]) (Coord⇒256 ∘ V2.y ∘ cursor $ app)
  ) app
mouseCallback button MouseButtonState'Released _ = id

cursorCallback : GLFW.CursorCallback ColorsApp
cursorCallback x y = set ፦[ cursor ] (screenToGl wh wh x y)

drawColorsApp : DrawApp ColorsApp
drawColorsApp = record
  { empty = emptyApp
  ; render = render
  ; frameCount = λ _ → 1
  ; nowFrame = λ _ → 0
  ; dontClearTexture = set ፦[ updated ] false
  ; getNeedToClearTexture = updated
  ; mouseCallback = GLFW.mouseCallbackWrap mouseCallback
  ; cursorCallback = GLFW.cursorCallbackWrap cursorCallback
  ; keyCallback = GLFW.keyCallbackWrap λ key scancode state mods → id
  }

main = run ∘ lift ∘ everything $ drawColorsApp
  where open IO
