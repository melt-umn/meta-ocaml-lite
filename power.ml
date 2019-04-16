let square = fun x -> x * x
in let rec spower = fun n x ->
     if n = 0 then .<1>.
     else if n mod 2 = 0 then .<square .~(spower (n/2) x)>.
     else .<.~x * .~(spower (n-1) x)>.
in let power7 = .! .<fun x -> .~(spower 7 .<x>.)>.
in power7 2
