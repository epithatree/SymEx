interval (a,b) = if a > b
                 then []
                 else a : interval(succ a,b)
