module Graphics.Vty.Image.Internal

import Derive.Prelude
import Graphics.Text.Width
import Graphics.Vty.Attributes

%default total
%language ElabReflection

||| This is the internal representation of Images.
|||
||| Images are:
|||
||| * a horizontal span of text
|||
||| * a horizontal or vertical join of two images
|||
||| * a two dimensional fill of the 'Picture's background character
|||
||| * a cropped image
|||
||| * an empty image of no size or content.
public export
data Image : Type where
  ||| A horizontal text span has a row height of 1.
  HorizText :
       (attr     : Attr)
    -> (text     : String)
    -> (outWidth : Nat)
    -> (numChars : Nat)
    -> Image

  ||| A horizontal join can be constructed between any two images.
  ||| However a HorizJoin instance is required to be between two images
  ||| of equal height. The horizJoin constructor adds background fills
  ||| to the provided images that assure this is true for the HorizJoin
  ||| value produced.
  HorizJoin :
       (left,right : Image)
    -> (outWidth, outHeight : Nat)
    -> Image

  ||| A veritical join can be constructed between any two images.
  ||| However a VertJoin instance is required to be between two images
  ||| of equal width. The vertJoin constructor adds background fills
  ||| to the provides images that assure this is true for the VertJoin
  ||| value produced.
  VertJoin :
       (top,bottom : Image)
    -> (outWidth, outHeight : Nat)
    -> Image

  ||| A background fill will be filled with the background char. The
  ||| background char is defined as a property of the Picture this
  ||| Image is used to form.
  BGFill : (outWidth, outHeight : Nat) -> Image

  ||| Crop an image
  Crop :
       (img : Image)
    -> (leftSkip, topSkip : Nat)
    -> (outWidth, outHeight : Nat)
    -> Image

  ||| The empty image
  Empty : Image

%runElab derive "Image" [Show,Eq]

||| The width of an Image. This is the number display columns the image
||| will occupy.
export
width : Image -> Nat
width (HorizText _ _ w _) = w
width (HorizJoin _ _ w _) = w
width (VertJoin _ _ w _)  = w
width (BGFill w _)        = w
width (Crop _ _ _ w _)    = w
width Empty               = 0

||| The height of an Image. This is the number of display rows the
||| image will occupy.
export
height : Image -> Nat
height (HorizText _ _ _ _) = 1
height (HorizJoin _ _ _ h) = h
height (VertJoin _ _ _ h)  = h
height (BGFill _ h)        = h
height (Crop _ _ _ _ h)    = h
height Empty               = 0

||| combines two images side by side
|||
||| Combines text chunks where possible. Assures outputWidth and
||| outputHeight properties are not violated.
|||
||| The result image will have a width equal to the sum of the two images
||| width. And the height will equal the largest height of the two
||| images. The area not defined in one image due to a height mismatch
||| will be filled with the background pattern.
export
horizJoin : Image -> Image -> Image
horizJoin Empty i     = i
horizJoin i     Empty = i
horizJoin i0@(HorizText a0 t0 w0 cw0) i1@(HorizText a1 t1 w1 cw1) =
  if a0 == a1
     then HorizText a0 (t0 ++ t1) (w0 + w1) (cw0 + cw1)
     else HorizJoin i0 i1 (w0 + w1) 1
horizJoin i0 i1 =
  let h0 := height i0
      h1 := height i1
      w0 := width  i0
      w1 := width  i1
      w  := w0 + w1
   in if      h0 == h1 then HorizJoin i0 i1 w h0
      else if h0 < h1 then
        let padAmount := h1 `minus` h0
         in HorizJoin (VertJoin i0 (BGFill w0 padAmount) w0 h1) i1 w h1
      else
        let padAmount := h0 `minus` h1
         in HorizJoin i0 (VertJoin i1 (BGFill w1 padAmount) w1 h0) w h0

||| Combines two images vertically
|||
||| The result image will have a height equal to the sum of the heights
||| of both images. The width will equal the largest width of the two
||| images. The area not defined in one image due to a width mismatch
||| will be filled with the background pattern.
export
vertJoin : Image -> Image -> Image
vertJoin Empty i     = i
vertJoin i     Empty = i
vertJoin i0    i1    =
  let w0 := width i0
      w1 := width i1
      h0 := height i0
      h1 := height i1
      h  := h0 + h1
   in if      w0 == w1 then VertJoin i0 i1 w0 h
      else if w0 < w1 then
        let padAmount := w1 `minus` w0
         in VertJoin (HorizJoin i0 (BGFill padAmount h0) w1 h0) i1 w1 h
      else
        let padAmount := w0 `minus` w1
         in VertJoin i0 (HorizJoin i1 (BGFill padAmount h1) w0 h1) w0 h

export
clipText : String -> Nat -> Nat -> String
clipText txt leftSkip rightClip =
  let cs        := unpack txt
      (drp,pre) := clipForCharWidth leftSkip cs 0
      cs2       := if pre then '…' :: drop (drp+1) cs else drop drp cs
      (tke,suf) := clipForCharWidth rightClip cs2 0
      cs3       := take tke cs2 ++ (if suf then ['…'] else [])
   in fastPack cs3

     where
       -- Note: some characters and zero-width and combining characters
       -- combine to the left, so keep taking characters even if the
       -- width is zero.
       --
       -- The returned pair indicates the number of characters to
       -- until the width (the first Nat) is filled. The bool indicates
       -- if we should prepend or appends triple dots to the clipped
       -- text.
       clipForCharWidth : Nat -> List Char -> Nat -> (Nat, Bool)
       clipForCharWidth _ []      n = (n,False)
       clipForCharWidth w (c::cs) n =
         let cw := charWidth c
          in if w < cw
                then (n, w /= 0)
                else clipForCharWidth (w `minus` cw) cs (S n)

export %inline
Semigroup Image where (<+>) = vertJoin

export %inline
Monoid Image where neutral = Empty
