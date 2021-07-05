type identifier = string

open Format
exception SyntaxError of string

type judgement =
  | JValue
  | JComp

let pp_judgement fmt = function
  | JValue -> pp_print_string fmt "val"
  | JComp -> pp_print_string fmt "comput"

type ttype =
  | TUnit
  | TArrow of ttype * ttype
  | TComp of ttype
  | TSum of ttype * ttype
  | TProduct of ttype * ttype
  | TRecursive of identifier * ttype
  | TVar of identifier
  | TMacro of identifier * ttype list

let rec pp_ttype fmt = function
  | TUnit -> pp_print_string fmt "1"
  | TArrow (t1, t2) -> fprintf fmt "(%a -> %a)" pp_ttype t1 pp_ttype t2
  | TComp t -> fprintf fmt "lazy(%a)" pp_ttype t
  | TSum (t1, t2) -> fprintf fmt "(%a + %a)" pp_ttype t1 pp_ttype t2
  | TProduct (t1, t2) -> fprintf fmt "(%a x %a)" pp_ttype t1 pp_ttype t2
  | TRecursive (id, t) -> fprintf fmt "rec(%s, %a)" id pp_ttype t
  | TVar s -> pp_print_string fmt s
  | TMacro _ -> assert false

type metatype = ttype * judgement

let pp_metatype fmt (a, b) = fprintf fmt "%a %a" pp_judgement b pp_ttype a

type term =
  | Unit
  | Variable of identifier
  | Computation of term
  | Abstraction of ttype * identifier * term
  | Return of term
  | Bind of term * identifier * term
  | Application of term * term
  | Force of term
  | Left of ttype * term
  | Right of ttype * term
  | Case of term * identifier * term * identifier * term
  | Tuple of term * term
  | Split of term * identifier * identifier * term
  | Fold of ttype * term
  | Unfold of term
  | Macro of identifier * ttype list * term list
  | Print_char of term

let rec pp_term fmt = function
  | Unit -> pp_print_string fmt "()"
  | Variable v -> pp_print_string fmt v
  | Computation t -> fprintf fmt "@[<hv 2>lazy(@,%a)@]" pp_term t
  | Abstraction (ttype, id, e) ->
    fprintf fmt "@[<hv 2>λ(%s : %a,@ %a)@]" id pp_ttype ttype pp_term e
  | Return t -> fprintf fmt "@[<hv 2>ret (@,%a)@]" pp_term t
  | Bind (t, id, e) -> fprintf fmt "@[<hv 2>let %s =@ %a@]@ in@ %a" id pp_term t pp_term e
  | Application (t1, t2) -> fprintf fmt "@[<hv 2>(@,%a@ .@ %a)@]" pp_term t1 pp_term t2
  | Force t -> fprintf fmt "@[<hv 2>force (@,%a)@]" pp_term t
  | Left (_, t) -> fprintf fmt "@[<hv 2>left(@,%a)@]"
                     pp_term t
  | Right (_, t) -> fprintf fmt "@[<hv 2>right(@,%a)@]"
                      pp_term t
  | Case (e, x1, e1, x2, e2) ->
    fprintf fmt "@[<hv 2>(match@ %a with@ left(%s) ->@ %a@ right(%s) ->@ %a)@]"
      pp_term e x1 pp_term e1 x2 pp_term e2
  | Tuple (t1, t2) -> fprintf fmt "@[<hv 2><%a,@ %a>@]" pp_term t1 pp_term t2
  | Split (e, x1, x2, e') ->
    fprintf fmt "@[<hv 2>(let <%s,%s> =@ %a@ in %a)@]"
      x1 x2 pp_term e pp_term e'
  | Fold (_, e) -> fprintf fmt "@[<hv 2>fold(@,%a)@]" pp_term e
  | Unfold e -> fprintf fmt "@[<hv 2>unfold(@,%a)@]" pp_term e
  | Macro (m, tyl, tl) ->
    let pp_sep fmt () = Format.fprintf fmt ",@ " in
    fprintf fmt "%s[%a](%a)" m (pp_print_list ~pp_sep pp_ttype) tyl
      (pp_print_list ~pp_sep pp_term) tl
  | Print_char e -> fprintf fmt "@[<hv 2>print (@,%a)@]" pp_term e

type command =
  | Declare of string * term
  | Type of string * ttype
  | DeclareMacro of string * string list * string list * term
  | Typemacro of string * string list * ttype
  | Check of term
  | Eval of term
  | Include of string

let rec tsubstitute subs t = match t with
  | TUnit -> TUnit
  | TVar id ->
    begin match List.assoc_opt id subs with
      | None -> t
      | Some replacement -> replacement
    end
  | TArrow (tau1, tau2) -> 
    TArrow (tsubstitute subs tau1, tsubstitute subs tau2)
  | TComp tau -> TComp (tsubstitute subs tau)
  | TSum (tau1, tau2) -> TSum (tsubstitute subs tau1, tsubstitute subs tau2)
  | TProduct (tau1, tau2) -> TProduct (tsubstitute subs tau1, tsubstitute subs tau2)
  | TRecursive (id, tau) ->
    TRecursive (id, tsubstitute (List.remove_assoc id subs) tau)
  | TMacro (id, tl) -> TMacro (id, List.map (tsubstitute subs) tl)

(* [substitute f t e] replaces variables named f in e by term t] *)
let rec substitute subs t = match t with
  | Unit -> Unit
  | Variable id ->
    begin match List.assoc_opt id subs with
      | None -> t
      | Some replacement -> replacement
    end
  | Computation c -> Computation (substitute subs c)
  | Abstraction (tt, id, a) ->
    Abstraction (tt, id, substitute (List.remove_assoc id subs) a)
  | Return r -> Return (substitute subs r)
  | Force r -> Force (substitute subs r)
  | Bind (t1, id, t2) ->
    Bind (substitute subs t1, id, substitute (List.remove_assoc id subs) t2)
  | Application (t1, t2) -> Application (substitute subs t1, substitute subs t2)
  | Right (ty, e) -> Right (ty, substitute subs e)
  | Left (ty, e) -> Left (ty, substitute subs e)
  | Case (e, x1, e1, x2, e2) ->
    let e' = substitute subs e in
    let e1' = substitute (List.remove_assoc x1 subs) e1 in
    let e2' = substitute (List.remove_assoc x2 subs) e2 in
    Case (e', x1, e1', x2, e2')
  | Tuple (t1, t2) -> Tuple (substitute subs t1, substitute subs t2)
  | Split (e1, x1, x2, e2) ->
    let e1' = substitute subs e1 in
    let e2' = substitute (List.remove_assoc x1 (List.remove_assoc x2 subs)) e2 in
    Split (e1', x1, x2, e2')
  | Fold (a, e) -> Fold (a, substitute subs e)
  | Unfold e -> Unfold (substitute subs e)
  | Macro (id, ttl, tl) -> Macro (id, ttl, List.map (substitute subs) tl)
  | Print_char e -> Print_char (substitute subs e)

let rec int_of_term = function
  | Fold (_, Right(_, next)) -> 1 + int_of_term next
  | Fold (_, Left(_, Unit)) -> 0
  | _ -> failwith "int_of_term got wrong structure"

let print_char_term e =
  let i = (int_of_term e) mod 256 in
  Printf.printf "%c%!" (Char.chr i)
