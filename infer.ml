open Unification
open Subs
open Ast


type 'a error = OK of 'a | Error of string

type typing_judgement = subst*expr*texpr

let report_not_unifiable te1 te2: (int * typing_judgement) error =
    Error("Not unifiable: " ^ (string_of_texpr te1) ^ " and " ^ (string_of_texpr te2))

let rec typeof (e: expr) (n: int ref) (tenv: subst): (int*typing_judgement) error =
    match e with
    | Int _ ->
            OK(!n, ((create ()), e, IntType))
    | Var x ->
            (* TODO: if x exists in tenv, return existed type *)
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
                            (* extend subst x (VarType (string_of_int !n)); *)
                            (* OK(!n, (subst, e, VarType (string_of_int !n))) *)
                            extend subst x (VarType x);
                            OK(!n, (subst, e, VarType x))
                        end)
    | Unit -> OK(!n, ((create ()), e, UnitType))

    | IsZero e0 ->
            (match typeof e0 n tenv with
                | OK(_, (subst_lower, _, te)) ->
                        ( match mgu [te, IntType] with
                            (* TODO: apply substitution to expression *)
                            | UOk subst ->
                                begin
                                    apply_to_env subst subst_lower;
                                    OK(!n, (subst_lower, e, BoolType))
                                end
                            | UError (te1, te2) -> report_not_unifiable te1 te2)
                | Error error_message -> Error(error_message))

    | Add(e1, e2)
    | Sub(e1, e2)
    | Mul(e1, e2)
    | Div(e1, e2) ->
            (match ((typeof e1 n tenv), (typeof e2 n tenv)) with
            | (OK(_, (subst1, _, te1)), OK(_, (subst2, _, te2))) ->
                begin
                    (* Printf.printf "te1: %s\n" (string_of_texpr te1); *)
                    let subst_lower = (join [subst1; subst2])
                    in (match mgu[(te1, IntType) ; (te2, IntType)] with
                        | UOk subst ->
                                begin
                                    (* Printf.printf "te1: %s\n" (string_of_texpr te1); *)
                                    (* Printf.printf "te2: %s\n" (string_of_texpr te2); *)
                                    (* Printf.printf "Op: %s\n" (string_of_subs subst_lower); *)
                                    apply_to_env subst subst_lower;
                                    OK(!n, (subst_lower, e, IntType))
                                end
                        | UError(te1, te2) -> report_not_unifiable te1 te2)
                end
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
                                | UError(te1, te2) -> report_not_unifiable te1 te2)
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
                    (match (typeof e2 n tenv) with
                    | OK(_, (subst2, _, te2)) ->
                            begin 
                                n := !n + 1;
                                let subst_lower = (join [subst1; subst2])
                                and return_type = VarType(string_of_int !n)
                                in (match (mgu [(te1, FuncType(te2, return_type)) ]) with
                                    | UOk subst ->
                                            begin
                                                apply_to_env subst subst_lower;
                                    (* Printf.printf "App te1: %s\n" (string_of_texpr te1); *)
                                    (* Printf.printf "app te2: %s\n" (string_of_texpr te2); *)
                                    (* Printf.printf "app Op: %s\n" (string_of_subs subst_lower); *)
                                                (* TODO *)
                                                OK(!n, (subst_lower, e, return_type))
                                            end
                                    | UError (te1, te2) -> report_not_unifiable te1 te2)
                            end
                    | Error em -> Error (em))
            | Error em -> Error(em))


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
