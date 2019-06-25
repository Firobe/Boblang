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
  | TComp t -> fprintf fmt "comp(%a)" pp_ttype t
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
  | Left of ttype * term
  | Right of ttype * term
  | Case of term * identifier * term * identifier * term
  | Tuple of term * term
  | Split of term * identifier * identifier * term
  | Fold of ttype * term
  | Unfold of term
  | Macro of identifier * ttype list * term list

let rec pp_term fmt = function
  | Unit -> pp_print_string fmt "()"
  | Variable v -> pp_print_string fmt v
  | Computation t -> fprintf fmt "@[<hv 2>comp(@,%a@]@,)" pp_term t
  | Abstraction (_, id, e) -> fprintf fmt "@[<hv 2>λ(%s,@ %a@]@,)" id pp_term e
  | Return t -> fprintf fmt "ret (%a)" pp_term t
  | Bind (t, id, e) -> fprintf fmt "@[<hv 2>let %s =@ %a@]@ in %a" id pp_term t pp_term e
  | Application (t1, t2) -> fprintf fmt "@[<hv 2>(@,%a@ . %a@]@,)" pp_term t1 pp_term t2
  | Left (_, t) -> fprintf fmt "@[<hv 2>left(@,%a@]@,)"
                     pp_term t
  | Right (_, t) -> fprintf fmt "@[<hv 2>right(@,%a@]@,)"
                      pp_term t
  | Case (e, x1, e1, x2, e2) ->
    fprintf fmt "@[<hv 2>(match@ %a with@ left(%s) ->@ %a@ right(%s) ->@ %a@]@,)"
      pp_term e x1 pp_term e1 x2 pp_term e2
  | Tuple (t1, t2) -> fprintf fmt "@[<hv 2><%a,@ %a@]@,>" pp_term t1 pp_term t2
  | Split (e, x1, x2, e') ->
    fprintf fmt "@[<hv 2>(let <%s,%s> =@ %a@ in %a@]@,)"
      x1 x2 pp_term e pp_term e'
  | Fold (_, e) -> fprintf fmt "@[<hv 2>fold(@,%a@]@,)" pp_term e
  | Unfold e -> fprintf fmt "@[<hv 2>unfold(@,%a@]@,)" pp_term e
  | Macro _ -> assert false

type command =
  | Declare of string * term
  | Type of string * ttype
  | DeclareMacro of string * string list * string list * term
  | Typemacro of string * string list * ttype
  | Check of term
  | Eval of term

let rec tsubstitute f t = function
  | TUnit -> TUnit
  | TVar id when id = f -> t
  | (TVar _) as v -> v
  | TArrow (tau1, tau2) -> 
    TArrow (tsubstitute f t tau1, tsubstitute f t tau2)
  | TComp tau -> TComp (tsubstitute f t tau)
  | TSum (tau1, tau2) -> TSum (tsubstitute f t tau1, tsubstitute f t tau2)
  | TProduct (tau1, tau2) -> TProduct (tsubstitute f t tau1, tsubstitute f t tau2)
  | (TRecursive (id, _)) as r when id = f -> r
  | TRecursive (id, tau) -> TRecursive (id, tsubstitute f t tau)
  | TMacro (id, tl) -> TMacro (id, List.map (tsubstitute f t) tl)

(* [substitute f t e] replaces variables named f in e by term t] *)
let rec substitute f t = function
  | Unit -> Unit
  | Variable v when v = f -> t
  | Variable v -> Variable v
  | Computation c -> Computation (substitute f t c)
  | Abstraction (_, id, _) as whole when id = f -> whole
  | Abstraction (tt, id, a) -> Abstraction (tt, id, substitute f t a)
  | Return r -> Return (substitute f t r)
  | Bind (t1, id, t2) ->
    Bind (substitute f t t1, id, if id = f then t2 else substitute f t t2)
  | Application (t1, t2) -> Application (substitute f t t1, substitute f t t2)
  | Right (ty, e) -> Right (ty, substitute f t e)
  | Left (ty, e) -> Left (ty, substitute f t e)
  | Case (e, x1, e1, x2, e2) ->
    let e' = substitute f t e in
    let e1' = if f = x1 then e1 else substitute f t e1 in
    let e2' = if f = x2 then e2 else substitute f t e2 in
    Case (e', x1, e1', x2, e2')
  | Tuple (t1, t2) -> Tuple (substitute f t t1, substitute f t t2)
  | Split (e1, x1, x2, e2) ->
    let e1' = substitute f t e1 in
    let e2' = if f = x1 || f = x2 then e2 else substitute f t e2 in
    Split (e1', x1, x2, e2')
  | Fold (a, e) -> Fold (a, substitute f t e)
  | Unfold e -> Unfold (substitute f t e)
  | Macro (id, ttl, tl) -> Macro (id, ttl, List.map (substitute f t) tl)
