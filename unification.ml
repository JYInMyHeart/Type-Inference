open Ast
open Subs


type  unif_result = UOk of Subs.subst | UError of texpr * texpr

let no_occur x y =
    match SetStr.find_opt x (fv_of_type y) with
    | Some _ -> false
    | None -> true

let rec mgu (texprs: (texpr * texpr) list) : unif_result =
    match texprs with
    | [] -> UOk (create ())
    | h::t ->
        (match h with
        | (BoolType, BoolType)
        | (IntType, IntType) -> mgu(t)
        | (VarType x, VarType y) ->
            (match mgu t with
            | UOk subst ->
                if x == y
                then UOk(subst)
                else begin
                    extend subst x (VarType y);
                    UOk(subst)
                end
            | UError (te1, te2) -> UError (te1, te2))
        | (VarType x, te) ->
            if (no_occur x te)
            then
            (match te with
            | VarType y when x == y-> mgu t
            | _ ->
                (match mgu t with
                | UOk subst ->
                    begin
                        extend subst x te;
                        UOk subst
                    end
                | UError(te1, te2) -> UError(te1, te2)))
            else UError(VarType x, te)

        | (te, VarType x) ->
            if (no_occur x te)
            then
                (match mgu t with
                | UOk subst ->
                    begin
                        (* Printf.printf "te = %s\n" (string_of_texpr te); *)
                        (* Printf.printf "x  = %s\n" x; *)
                        (* Printf.printf "subst = %s\n" (string_of_subs subst); *)
                        extend subst x te;
                        (* Printf.printf "subst = %s\n" (string_of_subs subst); *)
                        UOk subst
                    end
                | UError(te1, te2) -> UError(te1, te2))
            else UError(te, VarType x)

        | (RefType x, RefType y) ->
            mgu ((x, y)::t)

        | (FuncType(var1, body1), FuncType(var2, body2)) ->
            (match mgu[var1, var2] with
            | UOk subst_var ->
                (match mgu[body1, body2] with
                | UOk subst_body ->
                    (match mgu t with
                    | UOk subst -> UOk(join [subst_var; subst_body; subst])
                    | UError(te1, te2) -> UError(te1, te2))
                | UError(te1, te2) -> UError(te1, te2))
            | UError(te1, te2) -> UError(te1, te2))
        | (te1, te2) -> UError(te1, te2))
