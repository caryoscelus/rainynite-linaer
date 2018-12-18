{-- GLFW.agda - some bindings to Graphics.GPipe.Context.GLFW
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

module GLFW where

open import Data.Bool

open import Hask

{-# FOREIGN GHC import Graphics.GPipe.Context.GLFW #-}
  
postulate
  MouseButton ModifierKeys MouseButtonState : Set
  MouseButtonState'Pressed : MouseButtonState
  _==_ : (x y : MouseButtonState) → Bool

{-# COMPILE GHC MouseButton = type MouseButton #-}
{-# COMPILE GHC ModifierKeys = type ModifierKeys #-}
{-# COMPILE GHC MouseButtonState = type MouseButtonState #-}
{-# COMPILE GHC MouseButtonState'Pressed = MouseButtonState'Pressed #-}
{-# COMPILE GHC _==_ = (==) #-}

MouseCallback : Set → Set
MouseCallback App =
  (app : App)
  (button : MouseButton)
  (state : MouseButtonState)
  (mods : ModifierKeys)
  → App

MouseCallback′ : {M : Set} → Set → Set
MouseCallback′ {M} App =
  (modApp : (App → App) → M)
  (button : MouseButton)
  (state : MouseButtonState)
  (mods : ModifierKeys)
  → M

mouseCallbackWrap :
  ∀ {M App} → MouseCallback App → MouseCallback′ {M} App
mouseCallbackWrap f modApp button state mods =
  modApp (λ x → f x button state mods)

CursorCallback : Set → Set
CursorCallback App =
  (app : App)
  (x y : Double)
  → App

CursorCallback′ : {M : Set} → Set → Set
CursorCallback′ {M} App =
  (modApp : (App → App) → M)
  (x y : Double)
  → M

cursorCallbackWrap :
  ∀ {M App} → CursorCallback App → CursorCallback′ {M} App
cursorCallbackWrap f modApp x y = modApp (λ app → f app x y)
