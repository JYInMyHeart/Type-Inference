
let expr = function
  | 1 -> "x"
  | 2 -> "0"
  | 3 -> "x-1"
  | 4 -> "zero?(x)"
  | 5 -> "(f x)"
  | 6 -> "(f 0)"
  | 7 -> "(f 0)+1"
  | 8 -> "(0 f)" (*TODO: result : no unifiable: int and (VarTypef -> VarType2), but correct*)
  | 9 -> "((f 0) 1)"
  | 10 -> "f (0 2)" (* TODO: parser error *)
  | 11 -> "(((f x) y) z)"
  | 12 -> "(f ((x y) z))"
  | 13 -> "(f ((zero?(x) y) z))" (* TODO: not uni: bool and (VTy -> VT4), but correct*)
  | 14 -> "(f zero?(x))"
  | 15 -> "(x x)" (* TODO: succeeded, but invalid *)
  | 16 -> "proc(x) { x }"
  | 17 -> "(proc (x) { x } y)" (* TODO: not uni: VT1 and VTy *)
  | 18 -> "proc (s) { proc (x) { proc (y) { ((s x) y) }}}"
  | 19 -> "proc(s) { proc (x) { proc (y) { (s (x y)) }}}"
  | 20 -> "
let x = 7
in let y = 2
   in let y = let x = x-1
              in x-y
      in (x-8)- y"
  | 21 -> "
  let g =
     let counter = newref(0)
     in proc (d:int) {
         begin
          setref(counter, deref(counter)+1);
          deref(counter)
         end
       }
  in (g 11) - (g 22)"
  | 22 -> "let p = proc(x:int) { 5-x } in (p 3)"
  | 23 ->"
letrec fact (x) = if zero?(x) then 1 else x*(fact (x-1))
in (fact 7)"
  | 24 -> "
letrec infiniteLoop (x) = (infiniteLoop (x+1))
in let f = proc (z) { 11 }
in (f (infiniteLoop 0))"
  | n -> failwith @@ "Expression " ^string_of_int  n ^ " is not defined"

(* let test_all = *)
(*     let rec dummy i lst = *)
(*         if (i < 0) then lst *)
(*         else dummy (i - 1) ((Infer.inf (expr i))::lst) *)
(*     in dummy 24 [] *)
