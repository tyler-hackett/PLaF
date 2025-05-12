(*Names: Tyler Hackett, Justin Gajewski*)
open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) 
  | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | Unit -> return UnitType
  | NewRef(e) ->
    chk_expr e >>= fun t ->
    return @@ RefType(t)
  | DeRef(e) ->
    chk_expr e >>= fun t ->
    (match t with
     | RefType(t') -> return t'
     | _ -> error "deref: expected a reference type")
  | SetRef(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    (match t1 with
     | RefType(t1') -> 
       if t1' = t2
       then return UnitType
       else error "setref: type of value does not match reference type"
     | _ -> error "setref: expected a reference type")
  | BeginEnd([]) -> return UnitType
  | BeginEnd(es) ->
    let rec check_sequence = function
      | [] -> error "begin: empty sequence"
      | [e] -> chk_expr e
      | e::es -> 
        chk_expr e >>= fun _ ->
        check_sequence es
    in
    check_sequence es
  | EmptyList(Some t) -> return @@ ListType(t)
  | EmptyList(None) -> error "emptylist: type declaration missing"
  | Cons(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    (match t2 with
     | ListType(t2') ->
       if t1 = t2'
       then return @@ ListType(t1)
       else error "cons: type of head and tail do not match"
     | _ -> error "cons: expected a list type for second argument")
  | IsEmpty(e) ->
    chk_expr e >>= fun t ->
    (match t with
     | ListType(_) | TreeType(_) -> return BoolType
     | _ -> error "empty?: expected a list or tree type")
  | Hd(e) ->
    chk_expr e >>= fun t ->
    (match t with
     | ListType(t') -> return t'
     | _ -> error "hd: expected a list type")
  | Tl(e) ->
    chk_expr e >>= fun t ->
    (match t with
     | ListType(t') -> return @@ ListType(t')
     | _ -> error "tl: expected a list type")
  | EmptyTree(Some t) -> return @@ TreeType(t)
  | EmptyTree(None) -> error "emptytree: type declaration missing"
  | Node(de,le,re) ->
    chk_expr de >>= fun t1 ->
    chk_expr le >>= fun t2 ->
    chk_expr re >>= fun t3 ->
    (match t2, t3 with
     | TreeType(t2'), TreeType(t3') ->
       if t1 = t2' && t2' = t3'
       then return @@ TreeType(t1)
       else error "node: types of data and subtrees do not match"
     | _ -> error "node: expected tree types for left and right subtrees")
  | CaseT(target,emptycase,id1,id2,id3,nodecase) ->
    chk_expr target >>= fun t ->
    (match t with
     | TreeType(t') ->
       chk_expr emptycase >>= fun t_empty ->
       extend_tenv id1 t' >>+
       extend_tenv id2 (TreeType(t')) >>+
       extend_tenv id3 (TreeType(t')) >>+
       chk_expr nodecase >>= fun t_node ->
       if t_empty = t_node
       then return t_empty
       else error "caseT: types of empty and node cases do not match"
     | _ -> error "caseT: expected a tree type")
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

(* Custom pretty printer for type expressions *)
let rec string_of_texpr_simple = function
  | IntType -> "IntType"
  | BoolType -> "BoolType"
  | UnitType -> "UnitType"
  | FuncType(t1, t2) -> "FuncType(" ^ string_of_texpr_simple t1 ^ ", " ^ string_of_texpr_simple t2 ^ ")"
  | RefType(t) -> "RefType(" ^ string_of_texpr_simple t ^ ")"
  | ListType(t) -> "ListType(" ^ string_of_texpr_simple t ^ ")"
  | TreeType(t) -> "TreeType(" ^ string_of_texpr_simple t ^ ")"
  | PairType(t1, t2) -> "PairType(" ^ string_of_texpr_simple t1 ^ ", " ^ string_of_texpr_simple t2 ^ ")"
  | RecordType(fs) -> "RecordType(" ^ String.concat ", " (List.map (fun (id, t) -> id ^ ": " ^ string_of_texpr_simple t) fs) ^ ")"
  | UserType(id) -> id
  | _ -> "OtherType"

(* Type-check an expression and return a formatted string *)
let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr_simple t)
