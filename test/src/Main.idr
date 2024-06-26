module Main

import Data.String as S
import Graphics.Text.Width

%default total

main : IO ()
main = do
  for_ [the Bits32 0 .. 1114111] $ \v =>
    let chr := cast {to = Char} v
        w   := charWidth chr
     in when (w > 1) $
          putStrLn "\{padLeft 7 ' ' $ show v}: \{show w} (\{S.singleton chr})"
