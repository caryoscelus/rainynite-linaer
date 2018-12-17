{-- T.hs - some imperative opengl mess
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

{-# LANGUAGE
  NoMonomorphismRestriction,
  ScopedTypeVariables,
  TypeFamilies,
  LambdaCase,
  GADTs,
  FlexibleContexts
  #-}


module Main where

import Debug.Trace (traceShowId)
import Data.Maybe
import Data.Word (Word32)
import Graphics.GPipe
import qualified Graphics.GPipe.Context.GLFW as GLFW
import Data.IORef
import Control.Monad.IO.Class
import Control.Monad

import GL

foreverTil :: Monad m => m Bool -> m a -> m a
foreverTil cond m = do
  r <- m
  e <- cond
  if not e then
    foreverTil cond m
  else
    pure r

type Point = V2 Int

data Stroke = Stroke
  { sZoom :: Int
  , sPoints :: [Point]
  }

type Picture = [Stroke]

toTriangles :: Int -> Picture -> [V2 Float]
toTriangles zoom = foldr addStroke []
  where
    addStroke stroke vertices =
      let
        sp = sPoints stroke
        ss = zip sp (drop 1 sp)
        q = toZoom zoom (sZoom stroke)
      in
        (ss >>= drawLine q) <> vertices

zoomStep = 32
toZoom to from = 2 ** (fromIntegral (to - from) / zoomStep)

drawLine :: Double -> (Point, Point) -> [V2 Float]
drawLine _ (a , b) | a == b = []
drawLine q (a' , b') =
  let
    tt = realToFrac . (* q) . fromIntegral
    toQ = \(V2 x y) -> V2 (tt x) (tt y)
    a = toQ a'
    b = toQ b'
    dt = perp (signorm (a - b)) / 256
  in
    [ a-dt    , a+dt
              , b+dt
    , a-dt      
    , b-dt    , b+dt
    ]

v2to4 :: Num i => V2 i -> V4 i
v2to4 (V2 x y) = V4 x y 0 1

wh = 512


modifyAt :: Int -> (a -> a) -> [a] -> [a]
modifyAt n f l = take n l <> [f (l !! n)] <> drop (n + 1) l

main :: IO ()
main = runContextT GLFW.defaultHandleConfig $ do

  let
    frameCount = 24

  
  isDrawing <- liftIO $ newIORef False
  coords <- liftIO $ newIORef (V2 0 0)
  shapes <- liftIO $ newIORef (replicate frameCount [])
  zoomLevel <- liftIO $ newIORef 0
  requestClearTex <- liftIO $ newIORef True
  nowFrame <- liftIO $ newIORef 0


  frameTextures <-
    sequence . replicate frameCount $ newTexture2D RGB8 (V2 wh wh) 1

  let
    void = minBound :: Word32
    clearTex t = do
      writeTexture2D t 0 0 (V2 wh wh) (repeat (V3 void void void))

  let
    newShape = do
      zl <- readIORef zoomLevel
      fi <- readIORef nowFrame
      modifyIORef shapes (modifyAt fi (Stroke zl [] :))

    appendShape = do
      xy <- readIORef coords
      fi <- readIORef nowFrame
      modifyIORef shapes . modifyAt fi $ \(Stroke z ss : shapes) ->
        Stroke z (xy:ss) : shapes
  
  let wCfg = (GLFW.defaultWindowConfig "rainynite-linaer")
        { GLFW.configWidth = wh , GLFW.configHeight = wh }
  win <- newWindow (WindowFormatColor RGB8) wCfg

  let
    penColor = V3 0.5 0.5 0.5
    bgColor  = V3 0.0 0.0 0.0
    allColors = V3 True True True


  brushTexShader <- compileShader (singleColorOnTextureShader wh wh)

-- {-
  texShader <- compileShader $ do
    let
      filter = SamplerFilter Linear Linear Nearest Nothing
      edge = (pure ClampToEdge, 0)
    primStream <- toPrimitiveStream screenArea
    fragments <- rasterize
      (const (FrontAndBack, ViewPort (V2 0 0) (V2 wh wh), DepthRange 0 1))
      (fmap (\(V2 x y) -> (V4 (x*2-1) (y*2-1) 0 1, V2 x y)) primStream)
    samp <- newSampler2D (\s -> (screenTex s, filter, edge))
    let
      sampleTexture = sample2D samp SampleAuto Nothing Nothing
      fragments' = fmap sampleTexture fragments
    drawWindowColor
      (const (win, ContextColorOption NoBlending (pure True))) fragments'
-- -}


  GLFW.setMouseButtonCallback win . pure $ \button state mods -> do
    let
      pressed = state == GLFW.MouseButtonState'Pressed
    liftIO $ writeIORef isDrawing pressed
    when pressed $ newShape

  GLFW.setCursorPosCallback win . pure $ \x y -> do
    liftIO $ writeIORef coords (V2 (- wh `div` 2 + floor x) (wh `div` 2 - floor y))
    draw <- liftIO $ readIORef isDrawing
    when draw $ do
      appendShape

  GLFW.setKeyCallback win . pure $ \key i state mods -> do
    when (state /= GLFW.KeyState'Released) $ do
      writeIORef requestClearTex True
      case key of
        GLFW.Key'Equal -> modifyIORef zoomLevel succ
        GLFW.Key'Minus -> modifyIORef zoomLevel pred
        GLFW.Key'Left -> modifyIORef nowFrame ((`mod` frameCount) . pred)
        GLFW.Key'Right -> modifyIORef nowFrame ((`mod` frameCount) . succ)
        GLFW.Key'Z -> modifyIORef shapes (drop 1)
        _ -> pure ()

  wholeScreenBuff :: Buffer os (B2 Float) <- newBuffer 4
  writeBuffer wholeScreenBuff 0
    [ V2   0    0
    , V2   0    1
    , V2   1    1
    , V2   1    0
    ]

  foreverTil (fromMaybe False <$> GLFW.windowShouldClose win) $ do
    fi <- liftIO $ readIORef nowFrame
    picture <- fmap (!! fi) . liftIO $ readIORef shapes
    zl <- liftIO $ readIORef zoomLevel
    haveToClear <- liftIO $ readIORef requestClearTex

    let nowTex = frameTextures !! fi

    when haveToClear $ clearTex nowTex
    liftIO $ writeIORef requestClearTex False

    let
      lines = toTriangles (zl - 256) picture

    lineBuff :: Buffer os (B4 Float, B3 Float) <- newBuffer (length lines)
    unless (lines == []) $
      writeBuffer lineBuff 0 (fmap (\xy -> (v2to4 xy , penColor)) lines)

    render $ do
      vertexArray <- newVertexArray lineBuff
      let brushTriangles = toPrimitiveArray TriangleList vertexArray
      img <- getTexture2DImage nowTex 0
      brushTexShader (OnTexture img brushTriangles)

-- {-
    render $ do
      clearWindowColor win bgColor
      wholeScreen <- newVertexArray wholeScreenBuff
      let wholeScreenTriangles = toPrimitiveArray TriangleFan wholeScreen
      texShader (RenderTexture wholeScreenTriangles nowTex)
-- -}
    swapWindowBuffers win

    pure ()
