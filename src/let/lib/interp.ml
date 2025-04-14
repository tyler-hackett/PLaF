(**Tyler Hackett and Justin Gajewski*)

open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int n ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"

  | EmptyTree(_t) -> 
    return (TreeVal Empty)
  | Node(e1,e2,e3) ->
    eval_expr e1 >>= fun v1 ->
    eval_expr e2 >>= fun v2 ->
    eval_expr e3 >>= fun v3 ->
    (match (v2, v3) with
    | (TreeVal t2, TreeVal t3) -> 
      return (TreeVal (Node (v1, t2, t3)))
    | _ -> error "Node Error: The second and third argument must be a tree"
    )
  | IsEmpty(e) ->
    eval_expr e >>= (function
      | TreeVal Empty -> 
        return (BoolVal true)
      | TreeVal _ -> 
        return (BoolVal false)
      | _ -> error "IsEmpty Error: Expected a tree"
    )
  | CaseT(e1,e2,id1,id2,id3,e3) ->
    eval_expr e1 >>= (function
      | TreeVal Empty -> eval_expr e2
      | TreeVal (Node (v, l, r)) ->
        extend_env id1 v >>+
        extend_env id2 (TreeVal l) >>+
        extend_env id3 (TreeVal r) >>+
        eval_expr e3
      | _ -> error "CaseT Error: Expected a tree"
    )

  | Record(fs) ->
    let rec eval_fields fs acc =
      match fs with
      | [] -> return (RecordVal (List.rev acc))
      | (fname, (_, e)) :: rest ->
          eval_expr e >>= fun ev ->
          if List.mem_assoc fname acc
          then error ("Duplicate field: " ^ fname)
          else eval_fields rest ((fname, (false, ev)) :: acc)
    in
    eval_fields fs []
  | Proj(e, id) ->
    eval_expr e >>= fun ev ->
    (match ev with
      | RecordVal(fs) ->
          (try return (snd (List.assoc id fs))
          with Not_found -> error ("Field does not exist: " ^ id))
      | _ -> error "Proj: Expected a record")

  | _ -> failwith "Not implemented yet!"

(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e

(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


