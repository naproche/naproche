module Alice.Data.Tag where

data Tag =
  DIG | DMS | DMP | DHD | DIH | DCH | DEC |
  -- Tags to mark certain parts of function definitions
  DMK | DEV | DCD | DEF | DDM | DRP |
  -- Tags to mark parts in function proof tasks
  FDM | FEX | FUQ | FCH | FDC
  deriving (Eq, Show)

{- whether a Tag marks a part in a function proof task -}
fnTag :: Tag -> Bool
fnTag FDM = True; fnTag FCH = True; fnTag FEX = True; fnTag FUQ = True
fnTag _   = False