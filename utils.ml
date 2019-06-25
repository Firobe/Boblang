type identifier = string
[@@deriving show]

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
[@@deriving show {with_path=false}]

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
  | Macro of identifier * term list

let rec pp_term fmt = function
  | Unit -> pp_print_string fmt "()"
  | Variable v -> pp_print_string fmt v
  | Computation t -> fprintf fmt "@[<hv 2>comp(@,%a@]@,)" pp_term t
  | Abstraction (t, id, e) -> fprintf fmt "@[<hv 2>λ[%a](%s,@ %a@]@,)" pp_ttype
                                t id pp_term e
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
  | Fold (t, e) -> fprintf fmt "@[<hv 2>fold[%a](@,%a@]@,)" pp_ttype t pp_term e
  | Unfold e -> fprintf fmt "@[<hv 2>unfold(@,%a@]@,)" pp_term e
  | Macro _ -> assert false

type command =
  | Declare of string * term
  | Type of string * ttype
  | DeclareMacro of string * string list * term
  | Typemacro of string * string list * ttype
  | Check of term
  | Eval of term
