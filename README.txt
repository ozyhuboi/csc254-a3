Evan McLaughlin and Yibo Zhou 
CSC 254 Assignment 3 

Files Included: 
	a.out -> is a binary compiled with ocamlc for our file "intp.ml" and "str.cma"
	intp.ml -> our main source file 
	README.txt -> this 

Running Instructions: 
	For "a.out", simply type "a.out" on the command line and the binary should run. Sample output is below. 
	For "intp.ml", first enter the ocaml interpreter, then use command '#load "str.cma";;' followed by 
	'#use "inpt.ml";;' From there, you may use the 'parse : parse_table program' command generate a parse tree. 
	Then you may pass this parse tree into the 'ast_ize_P : parse_tree' program to generate a syntax tree. 
	The function 'interpret : ast input' takes in an ast and an input string and runs the interpreter on it. 
	If no input is desired, please enter simply "" as the input. Alternatively, you may use the 
	'ecg_run : program input'function that given a program and input string, will generate the parse tree 
	and ast with the ecg grammar and interpret it with the given input string. 

Abstract Syntax Tree Structure: 
    The syntax tree is built with the following attribute grammar: 
    P -> SL{P.val := SL.val}
    SL1 -> S{SL2.st := "SL1.st, S.val"} SL2{SL1.val := SL2.val}  
    SL -> e {SL.val := SL.st }
    S -> id := E {S.val := ":=, id, E.val"}
    S -> read id {S.val := "read id"}
    S -> write E {S.val := "write E.val"}
    S -> if C{SL.st := C.val} SL{S.val := "if, C.val, SL.val"} end 
    S -> while C{SL.st := C.val} SL{S.val := "while, C.val, SL.val"} end 
    C -> E1 == E2{C.val := "==, E1.val, E2.val"}
    C -> E1 != E2{C.val := "!=, E1.val, E2.val"}
    C -> E1 > E2{C.val := ">, E1.val, E2.val"}
    C -> E1 < E2{C.val := "<, E1.val, E2.val"}
    C -> E1 >= E2{C.val := ">=, E1.val, E2.val"}
    C -> E1 <= E2{C.val := "<=, E1.val, E2.val"}
    E -> T{TT.st := T.val} TT{E.val := TT.val}  
    TT1 -> + T{TT2.st := "+, TT1.st, T.val"} TT2{TT1.val := TT2.val}
    TT1 -> - T{TT2.st := "-, TT1.st, T.val"} TT2{TT1.val := TT2.val}
    TT -> e {TT.val := TT.st}
    T -> F{FT.st := F.val} FT{T.val := FT.val}
    FT1 -> * F{FT2.st := "*, FT1.st, F.val"} FT2{FT1.val := FT2.val}
    FT1 -> / F{FT2.st := "/, FT1.st, F.val"} FT2{FT1.val := FT2.val}
    FT -> e {FT.val := FT.st}
    F -> ( E ){F.val := E.val}
    F -> id{F.val := "id"}
    F -> lit{F.val := "lit"}

    Each branch of the ast will use matches in accordance to the attribute grammar where the ending 
    ".st" indicates a temporary sometimes sub-tree value while ".val" indicates an accumulated value 
    at a particular non-terminal. So the ast mostly matches parse tree non-terminal types up to return 
    certain abstract syntax tree types of ast_s, ast_c, and ast_e while ast_sl is just a list of ast_s's. 
    The ast_sl is returned up to ast_ize_P where it is returned as the syntax tree. 

Interpreter Structure: 
	The function interpret is split into the following subroutines; interpret_sl, interpret_s, 
	interpret_assign, interpret_read, interpret_write, interpret_if, interpret_while, interpret_expr, 
	and interpret_cond. The functions interpret_expr and interpret_cond take in the parameters expr:ast_e, 
	mem:memory and string:op, lo:ast_e, ro:ast_e respectively, both returning the variant type 'value'. 
	The variant type value can be three different types; Value of type int, Bool of type bool, and 
	Error of type string. The function interpret_expr will usually return Value of type int in 
	resolving expressions and interpret_cond will return Bool of type bool in resolving its conditions. 
	However, both may return Error of type string which is carefully matched up at every possible step 
	which an Error can occur to facilitate runtime exception handling, especially so certain Value to int 
	conversions happen properly. For interpret_if and interpret_while, each take in parameters cond:ast_c 
	sl:ast_sl representing the condition to be checked and the various statements in their body besides 
	the other inputs of the input list, memory, and output list. For interpret_if, after input validations, 
	a simple if statement is made to check if the condition is true. For interprete_while, after input 
	validation, the condition is checked for the body to run and interpret_while is run recursively afterward. 
	The functions interpret_write and interpret_read take in the parameters expr:ast_e and id:string 
	respectively, besides the usual inputs of input string, memory, and output string. The former will 
	append to the output string after validating and evaluating the expression. The latter will first 
	validate input, then take the first value from the input list, validate for only numeric input, 
	then append it to the memory for the id value. The interpret_assign takes in the parameters 
	lhs:ast_e and rhs:ast_e as expressions besides the usual input string, memory, and output string. 
	The function interpret_assign uses the helper function 
	'change_val : (old_mem:memory) (new_mem:memory) (id:string) (v:int)' which returns a new modified
	memory list from the old one by copying all of the tuples of the old memory into a new memory list 
	except for the memory tuple to be changed and appends the changed memory tuple to the new list 
	which is then returned. The function 'lookup_id : (mem:memory) (id:string)' is associated with 
	interpret_assign but used mostly in interpret_expr as it will look up a particular id in the 
	memory and recursively search for it until it either finds it and return the value, 
	or the list is empty, upon which returns a 'value not found' exception. 

Limitations: 
	Notice, during compilation you will get a lot of warnings for 'pattern-matching is not exhaustive' 
	for the particular case of Bool in type. Since the type for Bool can only be returned from 
	interpret_cond, the particular case in which the matching would be problematic would never occur, 
	thus the warning does not effect the proper running of the program. Also, since it occurs so 
	many times, we figured since it didn't effect the proper running, it wasn't worth our time to fix. 

Sample Output: 

	For the following: 
	print_string (interpret sum_ave_syntax_tree "4 6");
	(* should print "10 5" *)
	print_newline ();

	print_string (interpret primes_syntax_tree "10");
	(* should print "2 3 5 7 11 13 17 19 23 29" *)
	print_newline ();

	print_string (interpret sum_ave_syntax_tree "4 foo");
	(* should print "non-numeric input" *)
	print_newline ();
	print_string (ecg_run "write 3 write 2 / 0" "");
	(* should print "3 divide by zero" *)
	print_newline ();
	print_string (ecg_run "write foo" "");
	(* should print "foo: symbol not found" *)
	print_newline ();
	print_string (ecg_run "read a read b" "3");

	Output: 
	10 5 

	2 3 5 7 11 13 17 19 23 29 

	foo: non-numeric input 

	3 Error: divide by zero 

	foo : value not found

