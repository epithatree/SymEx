epsilon = subtract 1 . last . takeWhile (/= 1) . map (+ 1) . iterate (/2) $ 1
