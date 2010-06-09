-module ( lang1 ) . 
-export ( [run/1, compiler/0] ) . 


print ( X ) -> 
	io:format ( "~p~n" , [ X ] ) . 


make_table () -> 
	Tid = ets:new(myTable , [] ), 
	Store = fun ( Val ) -> 
		Key = make_ref () , 
		ets:insert ( Tid , { Key , Val } ) , 
		Key
		end , 
	Retrieve = fun ( Key ) -> 
		[{Key,Val} ] = ets:lookup ( Tid , Key ) , 
		Val 
		end , 
	{Store , Retrieve } . 

%cut ( I ,L ) - cuts the first I elements 
cut ( I , L ) when I >= 0 -> 
	{ R , L2 } = cut ( I , [] , L ) ,
	{ lists:reverse ( R ) , L2 }  .

cut ( 0 ,R , L ) -> 
	{ R , L } ; 

cut ( I , R , [H|L] ) when I> 0 -> 
	cut ( I-1 , [ H | R ] , L ) . 
	
% F : function , No_poped : arity , No_pushed : arity of return value 

stack_simple  ( F ) ->  
	stack_simple ( 1 ,1, F   ) . 


stack_simple  ( No_poped , No_pushed, F ) -> 
	fun 
		( Stack , RS, Cp ) -> 
			{Args , New_stack } = cut ( No_poped , Stack ) , 
			print ("%%%%%%%%%%"),print("Args" ), print ( Args ) , print ( New_stack  ) , 
			Ret_val = apply ( F , Args ) , 
			io:format ( "R : ~p~n" , [ Ret_val ] ) , print ( ">>>>>>>>>>>>>>>>>" ) , print ("") ,
			case No_pushed of 
				0 -> {  New_stack ,RS, Cp +1 } ; 
				1 -> {  [ Ret_val | New_stack ],RS, Cp +1  } ; 
				_ -> {  Ret_val ++ New_stack ,RS, Cp +1 } 
			end
		end . 

%compile time information 

makeL () -> 
	{ locals , 0 , dict:new() } . 

		
incL ( { locals , Current , Dict } ) -> 
	{ locals , Current + 1 , Dict }  .

decL ( { locals , Current , Dict } ) -> 
	{ locals , Current - 1 , Dict }  .

putL ( Name ,{ locals , Current , Dict } ) -> 
	Orig = case dict:find ( Name , Dict ) of 
		{ok , Val } -> Val ;
		error -> []
		end , 
	D3 = dict:store ( Name , [{ stack_var , Current}|Orig ]   , Dict ) , 
	{ locals , Current, D3 } . 

putLV ( Name ,Value,  { locals , Current , Dict } ) -> 
	Orig = case dict:find ( Name , Dict ) of 
		{ok , O } -> O ;
		error -> []
		end , 
	D3 = dict:store ( Name , [{ other , Value , Current}|Orig ]   , Dict ) , 
	{ locals , Current, D3 } . 

getL ( Name, { locals , Current , Dict } ) -> 
	[{stack_var, SL} |_] = dict:fetch ( Name , Dict ), 
	D = Current - SL , 
	if D<0 -> throw ( { error , "negative stack offset" } ); true-> D end .  

getLV ( Name, { locals , Current , Dict } ) -> 
	[{other, Value, SL}|_] = dict:fetch ( Name , Dict ), 
	D = Current - SL , 
	if D<0 -> throw ( { error , "negative stack offset" } ); true-> Value end .  
	 
remL ( Name , { locals , Current , Dict } ) -> 
	[_ | R ] = dict:fetch ( Name , Dict ) , 
	D2 = dict:store ( Name , R , Dict ) , 
	{ locals , Current , D2 } . 
%end of compile time 
	

collect_marks ( Code , Noop ) ->  %filters out {mark , M } and builds a dict with indexes to the position of the following instruction
	{C2 , Marks } = collect_marks (  Code  , 0 , dict:new(), Noop ) ,
	{C2  , Marks } . 

collect_marks ( [{ mark , M }| Code ] , I, D , Noop ) -> 
	D2 = dict:store ( M , I+1, D ) , 
	{ Rest , D3 } =  collect_marks ( Code, I + 1 , D2, Noop ), 
    { [ Noop | Rest ] , D3 }  ; 

collect_marks ( [X|Code ] , I , D , Noop) -> 
	{ Rest , D2 } = collect_marks ( Code , I+1 , D , Noop) , 
	{ [ X | Rest ], D2  } ; 

collect_marks ( [] , _ , D , _ ) -> 
	print ( marks ) ,
	print ( D ) , 
	{ [] , D } . 

fix_jumps ( Code, D )  -> 
	lists:map ( fun 
		( {jmp , J , M } ) -> J ( dict:fetch ( M , D ) ) ; 
		( X ) -> X 
		end , Code ) . 


free ( {constant , _ } ) -> 
	gb_sets:new () ;
free ( {variable , X } ) -> 
	gb_sets:singleton ( X ) ;
	      
free ( [ {bin_op , _} , E1 , E2 ] ) -> 
	gb_sets:union ( free (E1) , free (E2)  ) ; 
free ( [ 'let' ,  [ X , Cond  ] , E1  ] ) -> 
	gb_sets:difference ( 
		gb_sets:union ( lists:map ( fun free/1 , [ Cond , E1  ] )),
		gb_sets:singleton ( X ) ) ; 
free( [ 'if' , E1 , E2 ,E3 ] ) -> 
	gb_sets:union ( lists:map ( fun free/1 , [ E1,E2,E3 ] )); 
free ( [ 'lambda' , Args , Exp ] ) -> 
	gb_sets:difference ( free ( Exp )  , 
		gb_sets:union ( lists:map ( fun (X ) -> free ( X ) end , Args  ) ) )  ; 
free ( [ _|_ ] = L ) -> 
	gb_sets:union ( lists:map ( fun ( X ) -> free ( X ) end , L ) ) .
	
			

local_layout ( L  ) -> 
	lists:foldl (  fun ( X , Acc ) -> 
		putL ( X , incL (Acc ))  % hack - zero index is never used 
		end ,
		makeL(),
		L)  . 


fix_functions ( Code , Make_function ) -> 
	fix_functions ( Code , length ( Code ) , Make_function ) . 
% Warnig ! Last_index is meant to point to the first address that is not yet filled with code - 
% so unless this is turned to an Array afterwards, all function Pointers will be off by -1 

fix_functions ( [ {function , FCode } | RCode  ] , Last_index , Make_function  ) -> 
	[Make_function( Last_index )  ] ++ fix_functions ( RCode ++ FCode, Last_index + length ( FCode ) , Make_function);

fix_functions ( [ H| T ] , Last_index , Make_function ) -> 
	[ H ] ++ fix_functions ( T , Last_index , Make_function ) ; 
fix_functions ( [] , _,_ ) -> [] .


make_machine (Exp ) -> 
	{ Sto , Retr } = make_table()  , 

	Noop = stack_simple ( 0 , 0  , fun () -> foo end ) , 

	Loadc = fun ( C ) -> 
		stack_simple ( 0 ,1 ,fun () -> C end ) 
		end ,
	Add = stack_simple ( 2 ,1 , fun ( X , Y ) -> X+Y end ),
	Sub = stack_simple ( 2 ,1 , fun ( X , Y ) -> X-Y end ),
	Mul = stack_simple ( 2 ,1 , fun ( X , Y ) -> X*Y end ),
	PushLocal = fun ( I ) ->  % WARNING no stack abstraction 
			fun ( Stack , RS, Cp ) -> 
				NSTack = [ lists:nth( I +1 , Stack) | Stack ] ,  %one based indexing
				{ NSTack , RS, Cp +1  } 
				end 
		end ,
	Slide = fun ( I ) -> 
		fun ( Stack , RS, Cp ) -> 
			{ [X |_] , NSTack } = cut ( I + 1  , Stack ) ,
			{ [ X |NSTack] , RS , Cp +1 } 
			end 
		end , 
	Jump = fun ( I ) -> 
		fun ( Stack , RS, _ ) -> { Stack , RS, I } end
		end , 
	JumpNZ = fun ( I ) -> 
		fun ( [H|NStack] , RS, Cp ) -> 
			case H of 
				0 -> { NStack ,RS , Cp+1 } ;
				_ -> { NStack  ,RS, I } 
			end 
		end
		end , 
	JumpZ = fun ( I ) -> 
		fun ( [H|NStack], RS , Cp ) -> 
			case H of 
				0 -> { NStack , RS, I } ;
				_ -> { NStack , RS, Cp+1 }
			end 
		end
		end , 
	Call  = fun ( [Addr |Stack] , RetStack , Cp ) -> 
		{ Stack , [ Cp + 1 | RetStack ] , Addr  }
		end ,
	Ret = fun ( Stack , [ Addr |  RetStack  ] , _ ) -> 
		{ Stack , RetStack , Addr } 
		end , 
	Makevector = fun ( Free , Locals ) -> % copies a subset of the current stack into heap - indices determined at compile time 
		L = lists:map ( fun ( E ) -> getL ( E,Locals ) end, Free ) , % map names to indices 
		fun ( Stack , RS , Cp ) -> 
			io:format ( "free : ~p~n" , [ L ] ) , 
			V = lists:map ( fun ( E ) -> lists:nth ( E + 1 , Stack ) end , L  ) , %FIXME guess
			VRef = { vector , Sto ( V )} , 
			{ [VRef |Stack  ]  , RS , Cp +1 } 
		end 
		end , 
	PushvectorF = fun ( [{function , Addr , RefV } | RStack]  , RS , Cp ) -> 
		V = Retr ( RefV ) , 
		{ [Addr] ++ V ++ RStack , RS , Cp +1 } 
		end , 
	Makefunction = fun ( Addr ) -> 
		stack_simple ( 1 ,1 , fun ( {vector , Vref } ) -> 
			{ function , Addr , Vref } end )
			end , 
		
		

	
	Halt = fun ( [X|_] , _ , _) ->  X end , 


	CodeE_r = fun  % &*^%&^%#!!!!! cannot recurse on anonymus functions 
		( { constant , X  } , Locales, _  ) -> 
			{ [ Loadc(X) ] , incL ( Locales ) } ;

		( { variable , X  } , Locales, _  ) -> 
			{ [ PushLocal ( getL ( X , Locales )) ] , incL ( Locales ) } ; %sideffectfree -> don't care for evaluation order  :) 

		( [ 'let' , [{variable , Var} , VE] , E_  ] , L0 , R ) -> 
			{C1 , L1} = R ( VE , L0 , R ), 
			L2 = putL ( Var , L1 ) ,
			{C2 , L3 } = R ( E_ , L2 , R) , 
			{ C1 ++ C2++ [ Slide(1) ]  , remL ( Var ,decL (L3))  } ; 
		( [ 'if' , Cond , E1 , E2 ] , L0 , R ) -> 
			{ C_cond , L1 } = R ( Cond , L0 , R ) ,
			{ C_e1 , L2 } = R ( E1 , decL( L1) , R ) , % JumpZ consumes 1 
			{ C_e2 , L3 } = R ( E2 , decL( L1) , R  ) , 
			{ _L , _L } = { L2 , L3 } , %sanity check, local variables and stacklevel must be the same 
			M1 = make_ref () , M2 = make_ref () , 
			{ C_cond ++ [{jmp , JumpZ , M1}] ++ C_e1 ++[{jmp, Jump , M2},{mark , M1}] ++ C_e2 ++ [{mark , M2 } ] , L2 } ; 

		( [ {bin_op, O}  , X , Y ] , Locales , R ) -> 
			Fop = case O  of 
				'+' -> Add ; 
				'*' -> Mul ; 
				'-' -> Sub  
				end ,
			{ C1 , L1 } = R ( Y , Locales, R) , %stackorder 
			{ C2 , L2 } = R ( X , L1 , R ) , 
			{   C1 ++ C2++[ Fop ] , decL (L2)  }  ; 
			
		( [ 'lambda' , Args , Exp_ ] = F , Locals , R ) -> 
			Free = gb_sets:to_list ( free ( F ) ) , 
			All_vars = lists:map ( fun ( {variable , X} ) -> X ; ({ function , X })  -> X end ,Args )  
					++ lists:reverse( Free ) , 
			io:format ( "Free : {~p}~n" , [Free ] ) , 
			Flocal = local_layout ( All_vars  ) , 
			{ FCode , _ } = R ( Exp_ , Flocal , R )  , 
			Func = {function ,  FCode ++ [Slide ( length ( All_vars )+1), Ret  ]}, % +1 is the function object itself 
			{ [Makevector(Free, Locals ) ,Func] , incL ( Locals ) } ; 

		( DExp , Locales , R ) when is_list ( DExp )  ->  %everything else must be a function call 
			{ Args_code ,_  } = lists:foldl ( fun ( E , Acc ) -> 
				{ Code , Loc } = Acc ,
				{ TCode , TLoc } = R ( E , Loc , R ) ,
				{ Code ++ TCode , TLoc } 
				end ,
				{ [] , Locales } , DExp ) ,
			{Args_code ++ [PushLocal (length ( DExp )-1 ) , PushvectorF ,Call  ] , incL ( Locales ) } 

			
		end , 
	Dbg = fun ( E , L , R )  -> 
		io:format ( "args :~n~p~n~p~n~n~n" ,[ E, L  ] ) , 
		CodeE_r ( E , L , R ) 
		end, 
%	CodeE = fun ( E ) -> 
%		CodeE_r ( E, makeL () , CodeE_r ) 
%		end, 
	CodeE = fun ( E ) -> 
		Dbg ( E , makeL () ,  Dbg ) 
		end , 
	{ C, Locals } = CodeE ( Exp ) ,
	io:format ( "unfixed code : ~n~p~n" , [C ] ) , 
	C1 = fix_functions ( C  ++ [{ halt , Halt }] , Makefunction ) , 
	{ C2 , Marks  } = collect_marks ( C1 , Noop ) ,
	C3  = fix_jumps( C2 , Marks ) , 
	io:format ( "code : ~n~p~nLocals:~n~p~n" , [C3,Locals] ) , 
		
	array:from_list(  C3  )  .  



stackmachine_array ( Code , Cp , Stack, RetSt ) -> 
	case array:get(Cp, Code) of 
		{halt, Halt }  -> Halt ( Stack, RetSt , Cp ) ;  % to be able to abstract the stack layout 
		Inst -> 
			io:format ( "----------~nrunning : ~p on~n~p~n================~n",  [ Inst , Stack ] ) , 
			{  Nstack, NRetSt, Ncp  } = Inst ( Stack , RetSt, Cp  ) , 
			stackmachine_array ( Code , Ncp , Nstack, NRetSt ) 
	end . 


setin ( L ) -> 
	D = lists:foldl ( fun ( El , Acc ) ->  dict:append ( El , 1 , Acc ) end , dict:new() , L ) ,
	fun ( X ) -> 
		case dict:find ( X , D ) of 
			{ok , _ } -> true ;
			error -> false 
		end
	end .

lexabit ( X ) when is_integer ( X ) -> 
	{ constant , X } ; 
lexabit ( X ) when not is_list ( X ) -> 
	Keyword = setin ( ['let','if', 'lambda'] ) ,
	Binop = setin ( [ '+','-','*'] ) , 
	case Keyword ( X ) of 
		true -> X ;
		false -> case Binop ( X ) of 
			true -> {bin_op , X } ;
			false -> { variable , X }
		end 
	end ; 
lexabit (L ) -> 
	lists:map ( fun lexabit/1 , L ) . 

	



run ( Filename ) when is_atom ( Filename ) -> 
	{ ok , F } = file:open ( Filename , [ read ] ) , 
	{ ok , E }  =  io: read ( F , "" ) , 
	run ( E ) ;  

run ( E ) when is_list( E )  -> 
	E_ = lexabit ( E ) , 
	print ( "lexed version: " ) ,
	print ( E_ ) ,
	stackmachine_array ( make_machine ( E_ ), 0 , [], [] ) . 


compiler () -> 
	receive 
		start -> run ( lambda.lang1 ) ,
			compiler () 
	end . 


