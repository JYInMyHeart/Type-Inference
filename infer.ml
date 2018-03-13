open Unification
open Subs
open Ast


type 'a error = OK of 'a | Error of string

type typing_judgement = subst*expr*texpr

let report_not_unifiable te1 te2: (int * typing_judgement) error =
    Error("Not unifiable: " ^ (string_of_texpr te1) ^ " and " ^ (string_of_texpr te2))

let rec typeof (e: expr) (n: int ref): (int*typing_judgement) error =
    match e with
    | Int _ ->
            OK(!n, ((create ()), e, IntType))
    | Var x ->
            let subst = create ()
            in begin
                n := !n + 1;
                (* extend subst x (VarType (string_of_int !n)); *)
                (* OK(!n, (subst, e, VarType (string_of_int !n))) *)
                extend subst x (VarType x);
                OK(!n, (subst, e, VarType x))
            end

    | IsZero e0 ->
            (match typeof e0 n with
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
            (match ((typeof e1 n), (typeof e2 n)) with
            | (OK(_, (subst1, _, te1)), OK(_, (subst2, _, te2))) ->
                    let subst_lower = (join [subst1; subst2])
                    in (match mgu[(te1, IntType) ; (te2, IntType)] with
                        | UOk subst ->
                                begin
                                    apply_to_env subst subst_lower;
                                    OK(!n, (subst_lower, e, IntType))
                                end
                        | UError(te1, te2) -> report_not_unifiable te1 te2)
            | (Error error_message, _)
            | (_, Error error_message) -> Error(error_message)
            | (Error err1, Error err2) -> Error(err1 ^ " " ^ err2))

    | ITE(epred, e1, e2) ->
            (match typeof epred n with
            | OK(_, (subst_pred, _, tepred)) ->
                    (match ((typeof e1 n), (typeof e2 n)) with
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
                    | (_, Error error_message) -> Error(error_message)
                    | (Error err1, Error err2) -> Error(err1 ^ " " ^ err2))
            | Error em -> Error(em))


    (* | App(e1, e2) -> *)

    (* | Let(x, e1, e2) -> *)
    (*         (match (typeof e1 n) with *)
    (*         | (OK (_, (subst1, e1', te1)) -> *)
    (*                 (match mgu[VarType x, te1] with *)
    (*                 | UOk subst_mug1 -> *)
    (*                         (match (typeof (apply_to_expr subst e2)) with *)
    (*                         | OK (_, (subst2, e2', te2)) -> *)
    (*                                 | UOk subst_mug2 ->  *)
    | _ -> failwith "typeof: undefined"


let string_of_typing_judgement (tj: typing_judgement) =
    match tj with
    | subst, expr, texpr ->
            (string_of_expr expr) ^ ": " ^ (string_of_texpr texpr) ^ ", " ^ (string_of_subs subst)
    | _ -> failwith "Infer.string_of_typing_judgement: incorrect typing_judgement"

let infer_type (AProg e) =
    match typeof e (ref 0) with
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
