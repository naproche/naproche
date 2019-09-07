module SAD.Helpers where

-- | Remove a trailing line break from a string.
trimLine :: String -> String
trimLine "" = ""
trimLine "\n" = ""
trimLine "\r" = ""
trimLine "\r\n" = ""
trimLine (x:xs) = x : trimLine xs