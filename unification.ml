open Ast
open Subs


type  unif_result = UOk of Subs.subst | UError of texpr * texpr

let occur(x: string) (subst: subst): bool =
    let free_vars = (domain subst)
    in match List.find_opt (fun free_var -> free_var == x) free_vars with
       | Some _ -> true
       | None -> false

let rec mgu (texprs: (texpr * texpr) list) : unif_result =
    match texprs with
    | [] -> UOk (create ())
    | h::t ->
       (match h with
        | (BoolType, BoolType)
        | (IntType, IntType) -> mgu(t)
        | (VarType x, VarType y) ->
                if x == y then (mgu t) (* trivial pair elimination *)
                (* else (match (mgu t) with *)
                (*      | UOk subst -> *)
                (*              begin *)
                (*                  extend subst x (VarType y); *)
                (*                  UOk (subst) *)
                (*              end *)
                (*      | UError (te1, te2) -> UError(te1, te2)) *)
                (* TODO: unify two variables *)
                else UError(VarType x, VarType y)
        | (VarType x, te) ->
                let r = mgu(t)
                in (match r with
                    | UOk subst ->
                            begin
                                extend subst x te;
                                UOk(subst)
                            end
                    | UError (_, _) -> r))
    | _ -> failwith "Unification.mgu not implemented"
