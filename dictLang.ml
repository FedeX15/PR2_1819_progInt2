type ide = string;;
type exp = Eint of int | Ebool of bool | Estring of string | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | Edictionary of element list | Get of exp * ide | Set of exp * ide * exp | Rm of exp * ide | Clear of exp | ApplyOver of exp * exp
and element = Elem of ide * exp;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | String of string | Unbound | FunVal of evFun | RecFunVal of ide * evFun | Dictionary of element list
and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	"string" -> (match v with
		String(_) -> true |
		_ -> false) |
	"dictionary" -> (match v with
		Dictionary(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

let rec lookfor field d = match d with 
	Elem(chiave, valore)::resto -> (if chiave = field then valore
									else lookfor field resto) |
	[] -> failwith("Not found")
;;

let rec isthere dict field = match dict with 
	Elem(chiave, valore)::resto -> (if chiave = field then true
									else isthere resto field) |
	[] -> false
;;

(*Dictionary(Elem(field, value)::d)*)
let rec set dict field value = match dict with
	Elem(key, valore)::resto -> if key = field then Elem(key, value)::resto
								else Elem(key, valore)::(set resto field value) |
	[] -> failwith("Not found")
;;

let rec rm dict field = match dict with
	Elem(key, valore)::resto -> if key = field then resto
								else Elem(key, valore)::(rm resto field) |
	[] -> []
;;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Edictionary d -> Dictionary d |
	Eint n -> Int n |
	Ebool b -> Bool b |
	Estring s -> String s |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def")) |
    Get(dict, field) -> if (typecheck "dictionary" (eval dict r)) then (match (eval dict r) with
    							Dictionary(d) -> (eval (lookfor field d) r) |
    							Dictionary([]) -> failwith("not found")) 
    				   else failwith("nondictionary") |
    Set(dict, field, value) -> if (typecheck "dictionary" (eval dict r)) then (match (eval dict r) with
		    							Dictionary(d) -> if (isthere d field) then (Dictionary(set d field value))
														 else Dictionary(Elem(field, value)::d))
		    				   else failwith("nondictionary") |
	Rm(dict, field) -> if (typecheck "dictionary" (eval dict r)) then (match (eval dict r) with
										Dictionary(d) -> Dictionary(rm d field))
					   else failwith("nondictionary") |
	Clear(dict) -> if (typecheck "dictionary" (eval dict r)) then Dictionary([])
				   else failwith("nondictionary")
;;

let env0 = emptyenv Unbound;;

let emptydict = Edictionary([]);;
let iddict = Edictionary(Elem("nome", Estring("Federico"))::Elem("cognome", Estring("Matteoni"))::Elem("Matricola", Eint(530257))::[]);;
(*let iddict2 = Dictionary([Elem("nome", "Federico"); Elem("cognome", "Matteoni"); Elem("Matricola", 530257)]);;*)

let err = Get(iddict, "matricola");;
let nome = Get(iddict, "nome");;
let cognome = Get(iddict, "cognome");;
let matricola = Get(iddict, "Matricola");;
let iddict2 = Set(iddict, "eta", Eint 22);;
let dict2 = Set(emptydict, "prova", Estring("ASD"));;
let iddict3 = Set(iddict2, "Matricola", Eint 999999);;
let iddict4 = Rm(iddict3, "cognome");;
let dict3 = Rm(dict2, "nonesistente");;
let cleardict = Clear(iddict4);;

Printf.printf "\n\n****Dictionaries****\n";;
eval iddict env0;;
eval emptydict env0;;

Printf.printf "\n\n****Get****\n";;
eval nome env0;;
eval cognome env0;;
eval matricola env0;;

Printf.printf "\n\n****Set****\n";;
eval iddict2 env0;;
eval dict2 env0;;
eval iddict3 env0;;

Printf.printf "\n\n****Remove****\n";;
eval iddict4 env0;;
eval dict3 env0;;

Printf.printf "\n\n****Clear****\n";;
eval cleardict env0;;

Printf.printf "\n\n****Error*****\n";;
eval err env0;;