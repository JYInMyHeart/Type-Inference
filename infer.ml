open Unification
open Subs
open Ast


type 'a error = OK of 'a | Error of string

type typing_judgement = subst*expr*texpr

let report_not_unifiable te1 te2 e: (int * typing_judgement) error =
    Error("Not unifiable: " ^ (string_of_texpr te1) ^ " and " ^ (string_of_texpr te2) ^ " in " ^ (string_of_expr e))

let rec typeof (e: expr) (n: int ref) (tenv: subst): (int*typing_judgement) error =
    match e with
    | Int _ ->
            OK(!n, ((create ()), e, IntType))
    | Var x ->
        let subst = create ()
        in (match lookup tenv x with
            | Some tx ->
                begin
                    extend subst x tx;
                    OK(!n, (subst, e, tx))
                end
            | None ->
                begin
                    n := !n + 1;
                    extend subst x (VarType (string_of_int !n));
                    OK(!n, (subst, e, VarType (string_of_int !n)))
                end)
    | Unit -> OK(!n, ((create ()), e, UnitType))

    | IsZero e0 ->
        (match typeof e0 n tenv with
            | OK(_, (subst_lower, _, te)) ->
                ( match mgu [te, IntType] with
                    | UOk subst ->
                        begin
                            apply_to_env subst subst_lower;
                            OK(!n, (subst_lower, e, BoolType))
                        end
                    | UError (te1, te2) -> report_not_unifiable te1 te2 e)
            | Error error_message -> Error(error_message))

    | Add(e1, e2)
    | Sub(e1, e2)
    | Mul(e1, e2)
    | Div(e1, e2) ->
        (match ((typeof e1 n tenv), (typeof e2 n tenv)) with
        | (OK(_, (subst1, _, te1)), OK(_, (subst2, _, te2))) ->
            let subst_lower = (join [subst1; subst2])
            in (match mgu[(te1, IntType) ; (te2, IntType)] with
                | UOk subst ->
                    begin
                        apply_to_env subst subst_lower;
                        OK(!n, (subst_lower, e, IntType))
                    end
                | UError(te1, te2) -> report_not_unifiable te1 te2 e)
        | (Error error_message, _)
        | (_, Error error_message) -> Error(error_message))

    | ITE(epred, e1, e2) ->
        (match typeof epred n tenv with
        | OK(_, (subst_pred, _, tepred)) ->
            (match ((typeof e1 n tenv), (typeof e2 n tenv)) with
            | (OK(_, (subst1, _, te1)), OK(_, (subst2, _, te2))) ->
                let subst_lower = (join [subst_pred; subst1; subst2])
                in (match mgu[(tepred, BoolType) ; (te1, te2)] with
                    | UOk subst ->
                        begin
                            apply_to_env subst subst_lower;
                            (* TODO: apply subst to texpr *)
                            OK(!n, (subst_lower, e, te1))
                        end
                    | UError(te1, te2) -> report_not_unifiable te1 te2 e)
            | (Error error_message, _)
            | (_, Error error_message) -> Error(error_message))
        | Error em -> Error(em))

    | Let(x, e1, e2) ->
        (match (typeof e1 n tenv) with
        | OK(_, (subst1, _, te1)) ->
            let tenv_new = tenv
            in begin
                extend tenv_new x te1;
                (match typeof e2 n tenv_new with
                | OK(_, (subst2, _, te2)) ->
                    begin
                        remove subst1 x;
                        remove subst2 x;
                        OK(!n, (join [subst1; subst2], e, te2))
                    end
                | Error em -> Error(em))
            end
        | Error em -> Error em)

    | App(e1, e2) ->
        (match (typeof e1 n tenv) with
        | OK(_, (subst1, _, te1)) ->
            (match (typeof e2 n subst1) with
            | OK(_, (subst2, _, te2)) ->
                begin
                    n := !n + 1;
                    let subst_lower = (join [subst1; subst2])
                    and t_return = (match te1 with
                                    | FuncType (_, t_return) -> t_return
                                    | _ -> VarType(string_of_int !n))
                    in (match (mgu [(te1, FuncType(te2, t_return)) ]) with
                        | UOk subst ->
                            begin
                                apply_to_env subst subst_lower;
                                OK(!n, (subst_lower, e, apply_to_texpr subst t_return))
                            end
                        | UError (te1, te2) -> report_not_unifiable te1 te2 e)
                end
            | Error em -> Error (em))
        | Error em -> Error(em))

    | ProcUntyped(var_name, e_body) ->
        begin
            n := !n + 1;
            typeof (Proc(var_name, (VarType(string_of_int !n)), e_body)) n tenv
        end

    | Proc(var_name, t_var, e_body) ->
        let tenv_new = tenv
        in begin
            extend tenv_new var_name t_var;
            match typeof e_body n tenv with
            | OK(_, (subst, _, t_body)) ->
                begin
                    remove subst var_name;
                    OK(!n, (subst, e, FuncType(t_var, t_body)))
                end
            | Error em -> Error em
        end

    | NewRef(e_value) ->
        (match typeof e_value n tenv with
        | OK(_, (subst, _, te_value)) ->
            OK(!n, (subst, e, RefType(te_value)))
        | Error em -> Error em)

    | DeRef(e_ref) ->
        (match typeof e_ref n tenv with
        | OK(_, (subst, _, te_ref)) ->
            (match te_ref with
            | RefType te_value ->
                OK(!n, (subst, e, te_value))
            | _ -> Error ("Exptected ref type: " ^ string_of_expr e_ref ^ ", but got " ^ string_of_texpr te_ref))
        | Error em -> Error em)

    | SetRef(e_ref, e_value) ->
        (match  typeof e_ref n tenv with
        | OK(_, (subst_ref, _, te_ref)) ->
            (match typeof e_value n tenv with
            | OK(_, (subst_value, _, te_value)) ->
                (match mgu[te_ref, RefType(te_value)] with
                | UOk subst ->
                    let subst_lower = join [subst_ref; subst_value];
                    in begin
                        apply_to_env subst subst_lower;
                        OK(!n, (subst_lower, e, UnitType))
                    end
                | UError (te1, te2) -> report_not_unifiable te1 te2 e)
            | Error em -> Error em)
        | Error em -> Error em)

    | BeginEnd es ->
        (match es with
        | [] -> typeof Unit n tenv
        | eh::[] -> typeof eh n tenv
        | eh::ets ->
            (match typeof eh n tenv with
            | OK(_, (subst_h, _, teh)) ->
                begin
                    (match typeof (BeginEnd(ets)) n (join [subst_h; tenv]) with
                    | OK(_, (subst_ts, _, tets)) -> OK(!n, (join [subst_h; subst_ts], e, tets))
                    | Error em -> Error em)
                end
            | Error em -> Error em))

    | LetrecUntyped(proc_name, var_name, e_proc_body, e_body) ->
        begin
            n := !n + 2;
            let te_var = VarType (string_of_int (!n - 1))
            and te_res = VarType (string_of_int !n)
            and tenv_proc = tenv
            in begin
                (* extend tenv_new var_name t_var; *)
                extend tenv_proc proc_name (FuncType(te_var, te_res));
                (match typeof (Proc(var_name, te_var, e_proc_body)) n tenv_proc with
                | OK(_, (subst_proc, _, te_proc)) ->
                        let tenv_body = tenv
                        in begin
                            extend tenv proc_name te_proc;
                            (match typeof e_body n tenv_body with
                            | OK(_, (subst, _, te_body)) ->
                                OK(!n, (subst, e, te_body))
                            | Error em -> Error em)
                        end
                | Error em -> Error em)
            end
        end

    | _ -> failwith "typeof: undefined"


let string_of_typing_judgement (tj: typing_judgement) =
    match tj with
    | subst, expr, texpr ->
            (string_of_expr expr) ^ ": " ^ (string_of_texpr texpr) ^ ", " ^ (string_of_subs subst)

let infer_type (AProg e) =
    match typeof e (ref 0) (create ()) with
  | OK (_, tj) -> string_of_typing_judgement tj
  | Error s -> "Error! "^ s

let parse s =
    let lexbuf = Lexing.from_string s in
    let ast = Parser.prog Lexer.read lexbuf in
    ast


(* Interpret an expression *)
let inf (e:string) : string =
    e |> parse |> infer_type

let test (n:int) : string =
    Examples.expr n |> parse |> infer_type
