(*open Ast*)

(* invariant for substitutions: no id on a lhs occurs in any term earlier  *)
(* in the list                                                             *)
type substitution = (id * typ) list


let rec occurs (x : id) (t : typ) : bool =
match t with 
|TVar z -> if z = x then true else false 
|Arrow(z1, z2) -> occurs x z1 || occurs x z2 
;;

let rec subst (s : typ) (x : id) (t : typ) : typ = 
match t with 
|TVar y -> if x = y then s else t
|Arrow(x1, x2) -> Arrow(subst s x x1, subst s x x2) 
;;  

let rec apply (s : substitution) (t : typ) : typ =
match t with 
|TVar x -> if in_substitution s x then lookup s x else TVar x 
|Arrow(x1, x2) -> Arrow(apply s x1 , apply s x2) 
;; 

let rec lookup (s : substitution) (string_id : string) : typ = 
match s with 
|[] -> raise Error("Failed lookup, no substitution")
|h::t -> 
match h with 
|(a1, a2) -> if a1 = string_id then a2 else lookup t string_id 
;;

let rec in_substitution (subst: substitution) (tvar: string) : bool = 
match subst with 
|[] -> false 
|h::t -> 
match h with 
|(a1, a2) -> if a1 = tvar then true else in_substitution t tvar 
;;


let rec unify_one (t1 : typ) (t2 : typ) : substitution = 
  match t1 with
    | TVar a1 -> 
      if occurs a1 t2 then raise Error("Failed unification") else
      [(a1, t2)]
    | Arrow(u1, u2) -> 
    match t2 with 
      |Tvar b1 -> 
        if occurs b1 t2 then raise Error("Failed unification") else
        [(b1, t2)]
      |Arrow(v1, v2) ->
        unify([(u1,v1) ; (u2,v2)])        
and unify constraints =
  match constraints with 
  |[] -> []
  |h::t -> 
  match h with 
  | (p1, p2) -> 
    let sub = unify_one p1 p2 in  
      sub @ unify (apply_list sub t)  
;;

let rec apply_list (subst: subst) (constraints : (typ * typ) list) : (typ * typ) list = 
  match constraints with 
  |[] -> []
  |h::t -> 
  match h with 
  |(a1, a2)->
 (* let p1 = apply subst a1 
  let p2 = apply subst a2 in *)
  ((apply subst a1), (apply subst a2))::(apply_list subst t) 
;;


let infer (e : expr) : typ =
  Infer.reset_type_vars();
  match gather_constraints e [] with 
  |(type_of_e, constraints) -> 
     let hold = unify constraints in 
     apply hold type_of_e
;;  


let rec gather_constraints (x: expr) (context: (string * typ) list) : typ * (typ * typ) list = 
  match x with 
  | Fun(y, z) -> 
    begin
      let newvar = freshTVar () in
      match gather_constraints z ((y, newvar)::context)  with 
        | (type_of_z, new_constraints) ->
          (Arrow(newvar, type_of_z), new_constraints)
    end
  |Var v ->  (List.assoc v context, []) 
  |App(e1, e2)-> 
  begin
    match gather_constraints e1 context with
    | (type_of_e1, new_constraints_e1) ->
      begin 
      match gather_constraints e2 context with 
      |(type_of_e2, new_constraints_e2) -> 
          let inputType = freshTVar() in
          let outputType = freshTVar() in
          let t = Arrow(inputType, outputType) in
          let total_constraints = (t, type_of_e1) :: (inputType, type_of_e2) :: (new_constraints_e1 @ new_constraints_e2) in 
          (outputType, total_constraints)
      
      end

    end
;;
            
let counter = ref 0
let freshTvar () : typ = 
  begin
    counter := counter + 1;
    TVar("T" ^ (string_of_int (!counter)))
  end
;;









