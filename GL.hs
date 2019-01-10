{-- GL.hs - some semi-imperative opengl mess
 -- Copyright (C) 2018-2019 caryoscelus
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


module GL where

import Graphics.GPipe


data OnTexture what c = OnTexture
  { targetTexture :: Image (Format c)
  , putOnTexture :: what
  }

data RenderTexture os c p a = RenderTexture
  { screenArea :: PrimitiveArray p a
  , screenTex :: Texture2D os (Format c)
  }

sameV3 :: a -> V3 a
sameV3 x = V3 x x x

-- adopted from http://lolengine.net/blog/2013/07/27/rgb-to-hsv-in-glsl
hsvToRgb (V3 hue sat val) =
  let
    k = V3 1.0 (2.0 / 3.0) (1.0 / 3.0)
    (V3 r g b) =
      abs (fract' (sameV3 hue + k) * 6.0 - sameV3 3.0) - sameV3 1.0
  in
    (sameV3 val) *
      mix
        (sameV3 1.0)
        (V3 (saturate r) (saturate g) (saturate b))
        (sameV3 sat)

hsvTrianglesOnTextureShader
  :: Int -> Int
  -> Shader os
    (OnTexture (PrimitiveArray Triangles (B4 Float, B3 Float)) RGBFloat)
    ()
hsvTrianglesOnTextureShader w h = do
  stream <- toPrimitiveStream putOnTexture
  rasterized <- rasterize
    (const (FrontAndBack, ViewPort (V2 0 0) (V2 w h), DepthRange 0 1))
    stream
  draw (const NoBlending) rasterized $ \hsv ->
    drawColor
      (\s -> (targetTexture s, (V3 True True True), False))
      (hsvToRgb hsv ** 2.2)


colorTrianglesOnTextureShader
  :: Int -> Int
  -> Shader os
    (OnTexture (PrimitiveArray Triangles (B4 Float, B3 Float)) RGBFloat)
    ()
colorTrianglesOnTextureShader w h = do
  stream <- toPrimitiveStream putOnTexture
  rasterized <- rasterize
    (const (FrontAndBack, ViewPort (V2 0 0) (V2 w h), DepthRange 0 1))
    stream
  draw (const NoBlending) rasterized $ \color ->
    drawColor
      (\s -> (targetTexture s, (V3 True True True), False))
      (color ** 2.2) -- gamma correction, bah

singleTextureOnWindowShader
  :: Window os RGBFloat ds
  -> Int -> Int
  -> Shader os
    (RenderTexture os RGBFloat Triangles (B2 Float))
    ()
singleTextureOnWindowShader win w h = do
    let
      filter = SamplerNearest
      edge = (pure ClampToEdge, 0)
    primStream <- toPrimitiveStream screenArea
    fragments <- rasterize
      (const (FrontAndBack, ViewPort (V2 0 0) (V2 w h), DepthRange 0 1))
      (fmap (\(V2 x y) -> (V4 (x*2-1) (y*2-1) 0 1, V2 x y)) primStream)
    samp <- newSampler2D (\s -> (screenTex s, filter, edge))
    let
      sampleTexture = sample2D samp SampleAuto Nothing Nothing
      fragments' = fmap sampleTexture fragments
    drawWindowColor
      (const (win, ContextColorOption NoBlending (pure True))) fragments'
