open Ast

type subst = (string,Ast.texpr) Hashtbl.t

let create (_: unit) : subst =
    Hashtbl.create 100

let extend (subst: subst) (tvar: string) (texpr: texpr): unit =
    Hashtbl.add subst tvar texpr

let remove (subst: subst) (tvar: string): unit =
    Hashtbl.remove subst tvar

let lookup (subst: subst) (tvar: string): Ast.texpr option =
    Hashtbl.find_opt subst tvar

let rec apply_to_texpr (subst: subst) (texpr: texpr): texpr =
    match texpr with
    | IntType -> IntType
    | BoolType -> BoolType
    | UnitType -> UnitType
    | VarType id ->
       (let looked_type = lookup subst id in
            match looked_type with
            | Some t -> t
            | None -> texpr)
    | FuncType(t_var, t_body) ->
        FuncType(apply_to_texpr subst t_var, apply_to_texpr subst t_body)
    | RefType(t_ref) ->
        RefType(apply_to_texpr subst t_ref)

let rec apply_to_expr (subst: subst) (expr: expr): expr =
    match expr with
    | Proc(var_name, te_var, e_body) ->
        let te_var = (match lookup subst var_name with
                     | Some t -> t
                     | None -> te_var)
        in Proc(var_name, te_var, (apply_to_expr subst e_body))
    | _ -> expr

let apply_to_env (subst1: subst) (subst2: subst): unit =
    Hashtbl.iter
    (fun (key1: string) (value1: texpr) ->
        (Hashtbl.filter_map_inplace (fun (key2: string) (value2: texpr) ->
            if key1 == key2
            then Some(value1)
            else Some(apply_to_texpr subst1 value2)) subst2))
    subst1

let string_of_subs (subst: subst): string =
    "[" ^
    (Hashtbl.fold
        (fun (key: string) (value: texpr) (l: string) -> ("[ " ^ key ^ " : " ^ (string_of_texpr value) ^ " ]" ^ l))
        subst
        "")
    ^ "]"

let domain (subst: subst): string list =
    Hashtbl.fold (fun (key: string) (_: texpr) (l: string list) -> key :: l) subst []

let rec join (substs: subst list): subst =
    match substs with
    | [] -> (create ())
    | h::t ->
            let subst_back = join t
            in begin
                Hashtbl.iter (fun (key1: string) (value1: texpr) ->
                                match lookup subst_back key1 with
                                | None -> extend subst_back key1 value1
                                | Some te ->
                                    begin
                                        remove subst_back key1;
                                        extend subst_back key1 (apply_to_texpr h te)
                                    end) h;
                subst_back
            end



