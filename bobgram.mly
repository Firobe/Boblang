%token <string> ID
%token <string> MID
%token TYPE
%token DECLARE
%token TYPEMACRO
%token MACRO
%token CHECK
%token EVAL
%token ARROW
%token PLUS
%token ONE
%token UNIT
%token POINT
%token EQUAL
%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token LEFT_BRACKET
%token RIGHT_BRACKET
%token LEFT
%token FORCE
%token RIGHT
%token FOLD
%token REC
%token FUN
%token COLON
%token COMP
%token LETR
%token IN
%token UNFOLD
%token CASE
%token OF
%token RET
%token EOF
%token LETS
%token STAR

%start <Utils.command list> program

%%

program: l = command* EOF {l}

command:
| DECLARE; n = ID; EQUAL; t = term {Utils.Declare (n, t)}
| TYPE; n = ID; EQUAL; t = typ {Utils.Type (n, t)}
| MACRO; n = MID; LEFT_BRACKET; tparams = ID*; RIGHT_BRACKET;params = ID*;
    EQUAL; t = term {Utils.DeclareMacro (n, tparams, params, t)}
| MACRO; n = MID; params = ID*; EQUAL; t = term {Utils.DeclareMacro (n, [], params, t)}
| TYPEMACRO; n = MID; params = ID*; EQUAL; t = typ {Utils.Typemacro (n, params, t)}
| CHECK; t = term {Utils.Check t}
| EVAL; t = term {Utils.Eval t}

term:
| UNIT { Utils.Unit }
| COMP; LEFT_PAREN; t = term; RIGHT_PAREN { Utils.Computation t }
| FUN; LEFT_PAREN; x = ID; COLON; tau = typ; RIGHT_PAREN; ARROW; t = term
    { Utils.Abstraction (tau, x, t) }
| RET; LEFT_PAREN; t = term; RIGHT_PAREN { Utils.Return t }
| FORCE; LEFT_PAREN; t = term; RIGHT_PAREN { Utils.Force t }
| LETR; x = ID; EQUAL; e1 = term; IN; e2 = term
    { Utils.Bind (e1, x, e2) }
| t1 = term; POINT; t2 = term 
    { Utils.Application (t1, t2) }
| LEFT; LEFT_BRACKET; t = typ; RIGHT_BRACKET; LEFT_PAREN; e = term; RIGHT_PAREN
    { Utils.Left (t, e) }
| RIGHT; LEFT_BRACKET; t = typ; RIGHT_BRACKET; LEFT_PAREN; e = term; RIGHT_PAREN
    { Utils.Right (t, e) }
| CASE; e = term; OF; LEFT; LEFT_PAREN; x1 = ID; RIGHT_PAREN; ARROW;
    e1 = term; RIGHT; LEFT_PAREN; x2 = ID; RIGHT_PAREN; ARROW; e2 = term
    { Utils.Case (e, x1, e1, x2, e2) }
| FOLD; LEFT_BRACKET; tt = typ; RIGHT_BRACKET; LEFT_PAREN; t = term; RIGHT_PAREN
    { Utils.Fold (tt, t) }
| UNFOLD; LEFT_PAREN; t = term; RIGHT_PAREN { Utils.Unfold t }
| n = ID { Utils.Variable n }
| n = MID; LEFT_BRACKET; l1 = separated_nonempty_list (COMMA, typ);
    RIGHT_BRACKET;LEFT_PAREN; l2 = separated_nonempty_list(COMMA, term); RIGHT_PAREN
    { Utils.Macro (n, l1, l2) }
| n = MID; LEFT_PAREN; l = separated_nonempty_list(COMMA, term); RIGHT_PAREN
    { Utils.Macro (n, [], l) }
| LEFT_PAREN; t1 = term; COMMA; t2 = term; RIGHT_PAREN { Utils.Tuple (t1, t2) }
| LETS; LEFT_PAREN; x1 = ID; COMMA; x2 = ID; RIGHT_PAREN; EQUAL;
    e = term; IN; ee = term { Utils.Split (e, x1, x2, ee) }
| LEFT_PAREN; t = term; RIGHT_PAREN { t }

typ:
| ONE { Utils.TUnit }
| LEFT_PAREN; t1 = typ; ARROW; t2 = typ; RIGHT_PAREN { Utils.TArrow (t1, t2) }
| COMP; LEFT_PAREN; t = typ; RIGHT_PAREN { Utils.TComp t }
| LEFT_PAREN; t1 = typ; PLUS; t2 = typ; RIGHT_PAREN { Utils.TSum (t1, t2) }
| REC; LEFT_PAREN; x = ID; COMMA; t = typ; RIGHT_PAREN { Utils.TRecursive (x, t) }
| n = ID { Utils.TVar n }
| n = MID; LEFT_PAREN; l = separated_nonempty_list(COMMA, typ); RIGHT_PAREN
    { Utils.TMacro (n, l) }
| LEFT_PAREN; t1 = typ; STAR; t2 = typ; RIGHT_PAREN { Utils.TProduct (t1, t2) }
