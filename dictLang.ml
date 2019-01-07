type ide = string;;
type exp = Eint of int | Ebool of bool | Estring of string | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | Edictionary of (ide * exp) list | Get of exp * ide | Set of exp * ide * exp | Rm of exp * ide | Clear of exp | ApplyOver of exp * exp
;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | String of string | Unbound | FunVal of evFun | RecFunVal of ide * evFun | Dictionary of (ide * evT) list 
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

(*lookfor ha valore il valore associato a field all'interno di un dizionario d, altrimenti ha valore Failure("Not Found")*)
let rec lookfor field d = match d with 
	(chiave, valore)::resto -> (if chiave = field then valore
									else lookfor field resto) |
	[] -> failwith("Not found")
;;

(*isthere ha valore true se field è una chiave esistente all'interno di un dizionario dict, altrimenti ha valore false*)
let rec isthere dict field = match dict with 
	(chiave, valore)::resto -> (if chiave = field then true
									else isthere resto field) |
	[] -> false
;;

(*set ha valore dict con l'elemento di chiave field modificato con valore value*)
let rec set dict field value = match dict with
	(key, valore)::resto -> if key = field then (key, value)::resto
								else (key, valore)::(set resto field value) |
	[] -> failwith("Not found")
;;

(*rm ha valore dict da cui è stato rimosso l'elemento di chiave field*)
let rec rm dict field = match dict with
	(key, valore)::resto -> if key = field then resto
								else (key, valore)::(rm resto field) |
	[] -> []
;;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Edictionary(d) -> (let rec evalelement lista = match lista with
								(chiave, valore)::resto -> ((chiave, (eval valore r)))::(evalelement resto) |
								[] -> []
					  in (Dictionary(evalelement d))) |
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
    Get(dict, field) -> if (typecheck "dictionary" (eval dict r)) then (match (eval dict r) with (*Get exp * ide ha come valore il campo di chiave field contenuto in dict*)
    							Dictionary(d) -> lookfor field d |
    							Dictionary([]) -> failwith("not found")) 
    				   else failwith("nondictionary") |
    Set(dict, field, value) -> if (typecheck "dictionary" (eval dict r)) then (match (eval dict r) with (*Set exp * ide * exp ha valore un nuovo dizionario simile a dict ma con valore value all'interno dell'elemento di chiave field*)
		    							Dictionary(d) -> if (isthere d field) then (Dictionary(set d field (eval value r)))
														 else Dictionary((field, eval value r)::d))
		    				   else failwith("nondictionary") |
	Rm(dict, field) -> if (typecheck "dictionary" (eval dict r)) then (match (eval dict r) with (*Rm exp * ide ha valore un nuovo dizionario simile a dict da cui è stato rimosso l'elemento di chiave field*)
										Dictionary(d) -> Dictionary(rm d field))
					   else failwith("nondictionary") |
	Clear(dict) -> if (typecheck "dictionary" (eval dict r)) then Dictionary([]) (*Clear exp ha valore un nuovo dizionario vuoto*)
				   else failwith("nondictionary") |
	ApplyOver(funz, dict) -> if (typecheck "dictionary" (eval dict r)) then (match (eval dict r) with (*ApplyOver of exp * exp ha valore un nuovo dizionario simile a dict a cui è stata applicata la funzione funz ad ogni campo, se la funzione è applicabile a quel campo*)
										Dictionary(d) -> let rec funcallevalued (f : exp) (valore : evT) (r : evT env) : evT = (*Workaround: simile a FunCall ma non faccio eval sull'arg, che è già un evT*)
																let fClosure = (eval f r) in
																		(match fClosure with
																			FunVal(arg, fBody, fDecEnv) -> 
																				eval fBody (bind fDecEnv arg valore) |
																			RecFunVal(g, (arg, fBody, fDecEnv)) -> 
																				let aVal = valore in
																					let rEnv = (bind fDecEnv g fClosure) in
																						let aEnv = (bind rEnv arg aVal) in
																							eval fBody aEnv |
																			_ -> failwith("non functional value")) in let rec applyover funz dict = match dict with
																														(key, valore)::resto -> ((key, (try (funcallevalued funz valore r) with Failure("Type error") -> valore)))::( applyover funz resto) |
																														[] -> []
																													 in Dictionary(applyover funz d))
							 else failwith("nondictionary")
;;

(*TESTS*)

let env0 = emptyenv Unbound;; (*Ambiente di partenza, vuoto*)

let emptydict = Edictionary([]);; (*Dizionario vuoto*)
let iddict = Edictionary(("nome", Estring("Federico"))::("cognome", Estring("Matteoni"))::("Matricola", Eint(530257))::[]);; (*Dizionario misto*)
let intdict = Edictionary[("Uno", Eint 1); ("Dieci", Eint 10); ("Cento", Eint 100)];; (*Dizionario di interi*)

let err = Get(iddict, "matricola");; (*Errore perché il campo matricola non esiste all'interno di iddict*)
let nome = Get(iddict, "nome");;
let cognome = Get(iddict, "cognome");;
let matricola = Get(iddict, "Matricola");; (*Ottenimento dei valori associati alle chiavi indicate*)
let iddict2 = Set(iddict, "eta", Eint 22);;
let dict2 = Set(emptydict, "new", Estring("nuovo campo"));;
let iddict3 = Set(iddict2, "Matricola", Eint 999999);; (*Modifica dei campi associati alle chiavi indicate*)
let iddict4 = Rm(iddict3, "cognome");;
let dict3 = Rm(dict2, "nonesistente");; (*Rimozione di campo e di campo non esistente nel dizionario*)
let cleardict = Clear(iddict4);; (*Pulizia di dizionario*)
let incrementfunz = Fun("x", Sum(Den "x", Eint 1));; (*Funzione che aggiunge 1 ad un parametro x*)
let bigfunz = Fun("x", Sum(Den "x", Prod(Den "x", Eint 2)));; (*Funzione che da x associa (x+2x)*)
let applieddict = ApplyOver(incrementfunz, intdict);;
let applieddict2 = ApplyOver(bigfunz, applieddict);;
let appliediddict = ApplyOver(incrementfunz, iddict4);; (*Applicazione delle funzioni ai dizionari, solo ai campi compatibili (interi)*)
let moreoperationsdict = ApplyOver(bigfunz, ApplyOver(incrementfunz, Set(intdict, "Due", Eint 2)));;

(*Stampa dei dizionari di test iniziali*)
Printf.printf "\n\n****Dictionaries****\n";;
eval iddict env0;;
eval emptydict env0;;
eval intdict env0;;

(*Ottenimento di campi*)
Printf.printf "\n\n****Get****\n";;
eval nome env0;;
eval cognome env0;;
eval matricola env0;;

(*Modifica di campi*)
Printf.printf "\n\n****Set****\n";;
eval iddict2 env0;;
eval dict2 env0;;
eval iddict3 env0;;

(*Rimozione di campi*)
Printf.printf "\n\n****Remove****\n";;
eval iddict4 env0;;
eval dict3 env0;;

(*Pulizia di dizionari*)
Printf.printf "\n\n****Clear****\n";;
eval cleardict env0;;

(*Applicazione di funzioni*)
Printf.printf "\n\n****ApplyOver****\n";;
eval applieddict env0;;
eval applieddict2 env0;;
eval appliediddict env0;;
eval moreoperationsdict env0;;

(*Stampa dei dizionari iniziali*)
Printf.printf "\n\n****Original Dictionaries****\n";;
eval iddict env0;;
eval emptydict env0;;
eval intdict env0;;

(*Errori*)
Printf.printf "\n\n****Error*****\n";;
eval err env0;;