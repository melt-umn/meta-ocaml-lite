let twice = fun f x -> f (f x)
    in let inc = fun i -> i + 1
       in let neg = fun b -> if b then 1 = 0 else 0 = 0
          in (twice neg) (twice inc 0 = 2)
