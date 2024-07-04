module Graphics.Vty.Span

import Derive.Prelude
import Graphics.Text.Width
import Graphics.Vty.Attributes
import Graphics.Vty.Image
import Graphics.Vty.Image.Internal

%default total
%language ElabReflection

||| This represents an operation on the terminal: either an attribute
||| change or the output of a text string.
public export
data SpanOp : Type where

  ||| A span of UTF-8 text occupies a specific number of screen space
  ||| columns. A single UTF character does not necessarily represent 1
  ||| colunm. See module `Graphics.Text.Width`.
  TextSpan : Attr -> (outWidth, numChars : Nat) -> String -> SpanOp

  ||| Skips the given number of columns.
  Skip     : Nat -> SpanOp

  ||| Marks the end of a row. Specifies how many columns are
  ||| remaining. These columns will not be explicitly overwritten with
  ||| the span ops. The terminal is require to assure the remaining
  ||| columns are clear.
  RowEnd   : Nat -> SpanOp

||| A vector of span operations executed in succession. This represents
||| the operations required to render a row of the terminal. The
||| operations in one row may affect subsequent rows. For example,
||| setting the foreground color in one row will affect all subsequent
||| rows until the foreground color is changed.
public export
0 SpanOps : Type
SpanOps = List SpanOp

||| A List of span operation vectors for display, one per row of the
||| output region.
public export
0 DisplayOps : Type
DisplayOps = List SpanOps
--
-- dropOps :: Int -> SpanOps -> SpanOps
-- dropOps w = snd . splitOpsAt w

splitOpsAt : Nat -> SpanOps -> Maybe (SpanOps, SpanOps)
splitOpsAt = go [<]
  where
    go : SnocList SpanOp -> Nat -> SpanOps -> Maybe (SpanOps, SpanOps)
    go so 0       os     = Just (so <>> [], os)
    go so _       []     = Just (so <>> [], [])
    go so remCols (h::t) =
      case h of
        TextSpan a ow cs s => case remCols >= ow of
          True  => go (so :< h) (remCols `minus` ow) t
          False =>
            let preTxt    := clipText s 0 remCols
                preOp     := TextSpan a remCols (length preTxt) preTxt
                postWidth := ow `minus` remCols
                postTxt   := clipText s remCols postWidth
                postOp    := TextSpan a postWidth (length postTxt) postTxt
             in Just (so <>> [preOp], postOp :: t)
        Skip w             => case remCols >= w of
          True  => go (so :< Skip w) (remCols `minus` w) t
          False => Just (so <>> [Skip remCols], Skip (w `minus` remCols) :: t)
        RowEnd k           => Nothing

||| The number of columns the DisplayOps are defined for.
|||
||| All spans are verified to define same number of columns.
export
displayOpsColumns : DisplayOps -> Nat
displayOpsColumns []     = 0
displayOpsColumns (h::_) = length h

||| The number of rows the DisplayOps are defined for.
export %inline
displayOpsRows : DisplayOps -> Nat
displayOpsRows = length

export
affectedRegion : DisplayOps -> Region
affectedRegion ops = MkRegion (displayOpsColumns ops) (displayOpsRows ops)

||| The number of columns a SpanOps affects.
export
spanOpsAffectedColumns : SpanOps -> Nat
spanOpsAffectedColumns = foldl acc 0
    where
        acc : Nat -> SpanOp -> Nat
        acc t (TextSpan _ w _ _ ) = t + w
        acc t (Skip w)            = t + w
        acc t (RowEnd w)          = t + w

||| The width of a single SpanOp in columns.
export
spanOpHasWidth : SpanOp -> Maybe (Nat, Nat)
spanOpHasWidth (TextSpan _ ow cw _) = Just (cw, ow)
spanOpHasWidth (Skip ow)            = Just (ow,ow)
spanOpHasWidth (RowEnd ow)          = Just (ow,ow)

||| The number of columns to the character at the given position in the
||| span op.
export
columnsToCharOffset : Nat -> SpanOp -> Nat
columnsToCharOffset n (TextSpan _ _ _ s) = charsWidth (take n $ fastUnpack s)
columnsToCharOffset n (Skip _) = n
columnsToCharOffset n (RowEnd _) = n
