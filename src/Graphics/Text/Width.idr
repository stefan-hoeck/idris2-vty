module Graphics.Text.Width

%default total

%foreign "C:vty_mk_wcwidth,idris2-vty"
prim__vtyMkWcwidth : Char -> Int32

||| Returns the display width of a single character.
|||
||| Assumes all characters with unknown widths are 0 width.
export %inline
charWidth : Char -> Nat
charWidth = cast . prim__vtyMkWcwidth

export %inline
charsWidth : List Char -> Nat
charsWidth = foldl (\x,c => x + charWidth c) 0

||| Returns the display width of a string.
|||
||| Assumes all characters with unknown widths are 0 width.
export %inline
strWidth : String -> Nat
strWidth = charsWidth . fastUnpack
