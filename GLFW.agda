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
