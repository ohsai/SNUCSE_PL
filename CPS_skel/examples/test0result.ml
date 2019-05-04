(* Public testcase 5 : fibonacci with recursion. *)

(rec fib x => (fib (x + (-1))) + 1) 8


 ((rec x_2 x_1 => (fn x_16 => (fn x_17 => (fn x_18 => (x_16) ((x_17 + x_18)))(-1))(x_1)) (fn x_14 => (fn x_15 => (x_15) (x_2)) (fn x_13 =>  ((x_13) (x_14))+1))  ) (8))




== Running Input Program with M0 Interpreter ==
