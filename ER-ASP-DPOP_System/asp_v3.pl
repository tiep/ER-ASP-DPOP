%'read_from_stream_first should return false if unsatisfiable, now is return yes, but print out unsatisfiable'

:- module(asp, [solve_asp_models_given_list_files/2,solve_asp_models_given_stringfiles/2,solve_asp/2,solve_asp_models_given_files/2,solve_asp_models_in_fact_already_prepared/2,solve_asp_models_in_fact/2,assert_string_fact_to_module/2,retract_fact_from_module/2,retract_from_module/2,assert_fact_to_module/2,assert_to_module/2,load_MCS/3,compatible/2,compute_MCS/3,tiep/0,replace_first/4,split_1_char_br/3,close_str/0,retrieve_arc/0,start/0,show_dependency_tf/0,build_depend_tf/0,get_equil/1,show_dependency/0,make_dependency/1, asp_module/2, asp_module/3, use_asp/1,use_asp/2,use_asp_equil/1,use_asp_equil1/1,use_asp/3,
		print_models/1, print_equil/1, assert_asp/1, retract_asp/1, assert_asp_nb/1, retract_asp_nb/1, 
		total_models/2, model/3, models_asp/2, clear_all_modules/1, make_modul/4, cleanup_module/1]).
:- use_module(library(file_systems)).
:- use_module(library(sets)).
:- use_module(library(system)).
:- use_module(library(process)).
:- use_module(library(lists)).
:- use_module(library(codesio)).
:- use_module(library(varnumbers)).
:- use_module(library(terms)).

%:- op(600,xfy,::).
%:- op(601,xfy,>>).

:- op(1005,fx,$:-).
:- op(1002,xfx,$<).
:- op(1002,fx,$<).
:- op(1001,xfx,$>).
:- op(1001,xf,$>).

:- op(1002,xfx,$<<).
:- op(1002,fx,$<<).
:- op(1001,xfx,$>>).
:- op(1001,xf,$>>).

:- op(100,fx,not).
:- op(101,fx,domain).
%:- op(102,fx,hide).
:- op(103,fx,show).
:- op(104,xfx,/).
:- op(105,xfx,..).
:- op(106,xfx,<>).
:- op(120,fx,#).

:- call(unknown(_,fail)).

% no model due to inconsistency. Should be: e.g., domain(r,d). relation_value(r,x,y). if x/r does not belong to d then create a instance_of(r,d_0). ..............
% only get relation at level 1, should be recursived

get_relation_value(C):-
	process_class(C,Related_classes),

	absolute_file_name('$SHELL', Shell), 
	process_create(Shell, ['-c', ['sed -e \'1a instance_of(temp,',C,').\' rules-new.asp > ','tmp']], [process(P1)]),
	process_wait(P1,exit(0)),

	string_files(Related_classes,S1),
	atom_concat(S1,'tmp ',S),
	%atom_concat(S1,'rules-new.asp',S),
	%atom_concat(S2,'relations.asp',S),
	write(S),
	use_asp_qa(C,S).
	%delete_file('tmp').

individual_relation(X,Y,C):-
	get_relation_value(C),
	tmp1:instance_of(E,C),
	C:model(M), M:class(Y), 
	C:model(M), M:relation_value(X,E,F_E),
	tmp1:instance_of(F_E,Y1),
	C:model(M), M:subclass_of(Y1,Y).	

process_class(C,Related_classes):-
	atom_concat(C,'.asp',File),
	%load_files(File,[compilation_mode(assert_all)]),
	%asp:assert(instance_of(temp,C)),

	absolute_file_name('$SHELL', Shell), 
	process_create(Shell, ['-c', ['sed -e \'$a instance_of(temp,',C,'). #hide. #show subclass_of/2. #show instance_of/2.\' ',File,' > ','tmp.lp']], [process(P1)]),
	process_wait(P1,exit(0)),
	use_asp(tmp),
	delete_file('tmp.lp'),			
	findall(Class,(tmp1:instance_of(_,Class)|tmp1:subclass_of(C,Class)),Related_classes).

string_files([H|[]],String):- 
	atom_concat(H,'.asp ',String).

string_files([H1,H2|T],String):-
	atom_concat(H1,'.asp ',H1new),
	atom_concat(H1new,H2,NewHead),
	string_files([NewHead|T],String).

%descendant(X,Y):-
%	subclass_of(X,Y).
%descendant(X,Z):-
%	descendant(X,Y), subclass_of(Y,Z).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

asp_module(Header, Body):-
	parse_asp_module(Header, Body, Modulename),
	use_asp(Modulename,Body),
	absolute_file_name('$SHELL', Shell),
	atom_concat(Body,'.lp',Bodyfile),
	process_create(Shell, ['-c', ['cp ', 'asptmp ', Bodyfile]], [process(P1)]),
	process_wait(P1,exit(0)),
	process_create(Shell, ['-c', ['rm asptmp*']], [process(P2)]),
	process_wait(P2,exit(0)).

asp_module(Header, Body, Paras):-
	parse_asp_module(Header, Body, Modulename),
	use_asp(Modulename,Body, Paras),
	absolute_file_name('$SHELL', Shell),
	atom_concat(Body,'.lp',Bodyfile),
	process_create(Shell, ['-c', ['cp ', 'asptmp ', Bodyfile]], [process(P1)]),
	process_wait(P1,exit(0)),
	process_create(Shell, ['-c', ['rm asptmp*']], [process(P2)]),
	process_wait(P2,exit(0)).

parse_asp_module(Header, Body, Modulename):- 
	atom_concat(Header,'.lp',Headerfile),
	atom_concat(Body,'.lp',Bodyfile),
	absolute_file_name('$SHELL', Shell),
	/*get the Modulename of the asp_module*/
	file_member_of_directory(Headerfile,Fullname),
	current_module(Modulename,Fullname),
	/* process the qualifier of module */

	process_create(Shell, ['-c',['sed -e \'/use_module/! d\' -e \'s:\\/\\*.*::\' -e \'s/:- *use_module/fileTMP/\' ',Headerfile]], [stdout(pipe(Stream))]), 
	imported_module(Stream,Modulename),
	findall(X,(Modulename:fileTMP(X),X \== 'asp.pl'),L1), retractall(Modulename:fileTMP(_)),
	current_directory(Directory),
	findall(X1,(member(E,L1),atom_concat(Directory,E,F1),current_module(X2,F1),(X1=X2|findall(X3,X2:model(X3),X4),member(X1,X4))),List_of_module), 

	write(List_of_module), nl,
	findall((M,S),(member(M,List_of_module),current_predicate(M:P/A), functor(S,P,A), P \== skept, M:S), L),
	write(L),nl,

	findall((Mn,skept(Sn)),(member(Mn,List_of_module), findall(SubMn,Mn:model(SubMn),LsubMn), belongall(Sn,LsubMn)), Ln),
	write(Ln),nl,

	append(L,Ln,Lnew),	

	process_create(Shell, ['-c', ['cp ', Bodyfile, ' asptmp']], [process(P1)]),
	process_wait(P1,exit(0)),
	process_qualifier,
	%load_modules_into_asp_file(L),
	load_modules_into_asp_file(Lnew),
	process_create(Shell, ['-c', ['cp asptmp1', ' ', Bodyfile]], [process(P2)]),
	process_wait(P2,exit(0)).

belongall(S,[H|[]]):- current_predicate(H:P/A), functor(S,P,A), H:S.

belongall(S,[H|T]):- current_predicate(H:P/A), functor(S,P,A),
	H:S,
	belongall(S,T).

imported_module(Stream,Modulename):-
	\+ at_end_of_stream(Stream),
	read(Stream,L),	
	(L \== end_of_file
	->
	assert(Modulename:L), %write(L), nl,
	imported_module(Stream,Modulename)
	; 
	true).
 
stringasp0("sed -e '/^[^%]/s/\\([[:alnum:]]*\\) *: *\\([^-][[:alnum:]()]*\\)\\([^]}]*$\\)/contain(\\1,\\2)\\3/g' -e '/^[^%]/s/\\([[:alnum:]]*\\) *: *\\([^-][[:alnum:]()]*\\)\\([^]}]*$\\)/contain(\\1,\\2)\\3/g' -e '/^[^%]/s/\\([[:alnum:]]*\\) *: *\\([^-][[:alnum:]()]*\\)\\([^]}]*$\\)/contain(\\1,\\2)\\3/g' asptmp > asptmp1").

process_qualifier:-
	absolute_file_name('$SHELL', Shell),
	stringasp0(A), name(X,A),
	process_create(Shell, ['-c', [X]], [process(P1)]),
	process_wait(P1,exit(0)).

load_modules_into_asp_file([]):-
	open(asptmp1, append, S1),
	write(S1, '#hide contain/2.'),
	nl(S1),
	close(S1).


load_modules_into_asp_file([H|T]):-
	open(asptmp1, append, S1),
	write(S1, 'contain('),
	write(S1, H),
	write(S1, ').'),
	nl(S1),
	close(S1),
	load_modules_into_asp_file(T).
	
%--------clear_module/1 will clear all predicates in the module
clear_module(M) :-
	(current_predicate(M:P/A),
	abolish(M:P/A),
	fail
	;true
	). 

%--------clear_modules/3 will clear all predicates in the modules
clear_modules(M,N,I) :-
	(Nt is N+1,
	I==Nt	
	-> 
	true
	;
	It is I+48,
	char_code(Atom,It),
	atom_concat(M,Atom,M1),
	clear_module(M1),
	J is I+1,
	clear_modules(M,N,J)).

clear_all_modules(M):-
	findall(X, M:model(X), L),
	clear_module(M),
	member(T,L),
	clear_all_modules(T).

cleanup_module(M):-
	findall(X, M:model(X), L),
	clear_module(M),
	member(T,L),
	clear_module(T),
	fail.

cleanup_module(_).

%-------- make_modul/4 will create a module Name containing name of models, and create modules containing models of Name.lp
make_modul(Name,List,N,I):-
	(Nt is N+1,
	I==Nt	
	-> 
	true
	;
	nth1(I,List,Model),
	length(Model,N1),
	number_codes(I,CodeI),
	name(Name,CodeName),
	append(CodeName,CodeI,Code),
	name(Modulname,Code),
	assert(Name:model(Modulname)),
	make_submodul(Model,N1,1,Modulname),
	I1 is I+1,	
	make_modul(Name,List,N,I1)).

make_submodul(Model,N1,J,Modulname):-
	(N1t is N1+1,
	J==N1t
	-> 
	true
	;
	nth1(J,Model,Element),
	assert(Modulname:Element),
	J1 is J+1,
	make_submodul(Model,N1,J1,Modulname)).	

%stringasp3("sed -e '/%\\*/,/\\*%/d' -e 's:%.*::' plan_A.lp|sed -e 's/\\.\\./@@/g' -e 's/! =/<>/g' -e 's/\\.\\([^\\n]\\)/\\.\\n\\1/g'|sed -e 's/^[ \\t]*//'|sed -e 's/{/$</g' -e 's/}/$>/g' -e 's/\\[/$<</g' -e 's/\\]/$>>/g' -e 's/^:-/$:-/g' -e 's/\\([^.]*\\)\\./:-assert((\\1))./g' -e 's/@@/\\.\\./g' -e '/^$/d' > tmp").

substring1("sed -e '/%\\*/,/\\*%/d' -e 's:%.*::' ").
substring2("|sed -e 's/\\.\\./@@/g' -e 's/! =/<>/g' -e 's/\\.\\([^\\n]\\)/\\.\\n\\1/g'|sed -e 's/^[\\t]*//'|sed -e 's/{/$</g' -e 's/}/$>/g' -e 's/\\[/$<</g' -e 's/\\]/$>>/g' -e 's/^:-/$:-/g' -e 's/^-/negneg/g' -e 's/\\([^.]*\\)\\./:-assert(rule((\\1)))./g' -e 's/@@/\\.\\./g' -e '/^$/d' > ").

create_prolog_module(Name):-
	atom_concat(Name,'.lp',Name1),
	atom_concat(Name,'module',Name2),
	atom_concat(Name,'tmp',TmpFile),

	substring1(A), substring2(B), 
	name(A1,A), name(B1,B),
	(file_exists(TmpFile) -> CurrentFile=TmpFile; CurrentFile=Name1),

	atom_concat(A1,CurrentFile,R1),
	atom_concat(R1,B1,R2),
	atom_concat(R2,Name2,R),
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', [R]], [process(P1)]),
	process_wait(P1,exit(0)),
	Name2:compile(Name2),
	assert(convertedTMP(Name)),
	process_create(Shell, ['-c', ['rm ', Name2]], [process(P2)]),
	process_wait(P2,exit(0)).
	
%	findall(S,(current_predicate(Name2:X/Y), functor(S,X,Y), Name2:S), L),
%	write(L).

substring3("sed -e 's/-(\\(.*\\))/-\\1/' -e 's/<>/! =/g' -e 's/$</{/g' -e 's/$>/}/g' -e 's/$<</\\[/g' -e 's/$>>/\\]/g' -e 's/$:-/:-/g' -e 's/^negneg/-/g' -e 's/(\\(.*}\\))/\\1/g' ").

create_asp_file(Name):-
	atom_concat(Name,'tmp',Name1),
	atom_concat(Name,'module',Name2),
	findall(E,Name2:rule(E),L),
	open(Name2, write, S1),
	write_term_to_file(S1,L),
	close(S1),
	substring3(A), name(A1,A),
	atom_concat(A1,Name2,R1),
	atom_concat(R1,' > ',R2),
	atom_concat(R2,Name1,R3),
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', [R3]], [process(P1)]),
	process_wait(P1,exit(0)),
	process_create(Shell, ['-c', ['rm ', Name2]], [process(P2)]),
	process_wait(P2,exit(0)).

%--------predicate assert_asp/1: ...
assert_asp(Refname:P):-
	refTMP(Refname,Name),
	atom_concat(Name,'module',Name1),
	(on_exception(Err1, convertedTMP(Name), (Err1 = existence_error(_,_))) -> true;create_prolog_module(Name)),
	assert(Name1:rule(P)),
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)).

assert_asp(Refname:P):-
	refTMP(Refname,Name),
	atom_concat(Name,'module',Name1),
%	(on_exception(Err1, convertedTMP(Name), (Err1 = existence_error(_,_))) -> true;create_prolog_module(Name)),
	retract(Name1:rule(P)),
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)),
	fail.

assert_asp_nb(Refname:P):-
	refTMP(Refname,Name),
	atom_concat(Name,'module',Name1),
	(on_exception(Err1, convertedTMP(Name), (Err1 = existence_error(_,_))) -> true;create_prolog_module(Name)),
	assert(Name1:rule(P)),
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)).

%--------predicate retract_asp/1: ...
retract_asp(Refname:P):-
	refTMP(Refname,Name), 
	atom_concat(Name,'module',Name1),
	(on_exception(Err1, convertedTMP(Name), (Err1 = existence_error(_,_))) -> true;create_prolog_module(Name)),

	(on_exception(Err2, retractTMP(rule(P2)), (Err2 = existence_error(_,_))) 	% in cases we use retract_asp without 
	->										% backtracking, and some other rules
	functor(P,N,A), functor(P2,N,A), 						% will use retract_asp again
	retractall(retractTMP(rule(P2)))
	; 
	true
	),

	retract(Name1:rule(P)), 							% choicepoint
	(on_exception(Err2, retractTMP(rule(P1)), (Err2 = existence_error(_,_))) 
	->
	functor(P,N,A), functor(P1,N,A), 
	assert(Name1:rule(P1)), %write(P1), write(' is undone!'), nl, 
	retractall(retractTMP(rule(P1)))
	; 
	true
	),
	assert(retractTMP(rule(P))), % write(P), nl,
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)).

retract_asp(Refname:P):-
	refTMP(Refname,Name),
	atom_concat(Name,'module',Name1),
	(on_exception(Err2, retractTMP(rule(P)), (Err2 = existence_error(_,_))) 	
	->										
	assert(Name1:rule(P)), %write(P), write(' is undone!'), nl, 
	retractall(retractTMP(rule(P))), 
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)), fail	
	; 
	fail
	).

retract_asp_nb(Refname:P):-
	refTMP(Refname,Name),
	atom_concat(Name,'module',Name1),
	(on_exception(Err1, convertedTMP(Name), (Err1 = existence_error(_,_))) -> true;create_prolog_module(Name)),
	retract(Name1:rule(P)),
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)).

/*
retract_asp(Refname:P):-
	refTMP(Refname,Name),
	atom_concat(Name,'module',Name1),
	(on_exception(Err1, convertedTMP(Name), (Err1 = existence_error(_,_))) -> true;create_prolog_module(Name)),
%	Name1:clause(rule(P),true),
	retract(Name1:rule(P)), 
	(on_exception(Err2, retractTMP(rule(P1)), (Err2 = existence_error(_,_))) 
	->
	functor(P,N,A), functor(P1,N,A), 
	assert(Name1:rule(P1)), % write(P), write(' is undone!'), nl, 
	retractall(retractTMP(rule(P1)))
	; 
	true
	),
	assert(retractTMP(rule(P))), % write(P), nl,
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)).

retract_asp(Refname:P):-
	refTMP(Refname,Name),
	atom_concat(Name,'module',Name1),
	retractTMP(rule(P)),  	
	assert(Name1:rule(P)), % write(P), write(' is undone!'), nl, 
	retractall(retractTMP(P)), 
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)), fail.

retract_asp_nb(Refname:P):-
	refTMP(Refname,Name), 
	atom_concat(Name,'module',Name1), %write('okok'),nl,
	(on_exception(Err1, convertedTMP(Name), (Err1 = existence_error(_,_))) -> true;create_prolog_module(Name)),
%	write('choicepoint'),nl,
	retract(Name1:rule(P)), % write(P), nl,
	create_asp_file(Name),
	(on_exception(Err1, parasTMP(Refname,Paras), (Err1 = existence_error(_,_))) 
 	-> 
	use_asp(Refname,Name,Paras)
	;
	use_asp(Refname,Name)).
*/
%retract_asp_nb(_:_):- fail.

write_term_to_file(_,[]). 

write_term_to_file(S1,[H|T]):-
%	open(TmpFile, append, S1),
%	(ground(H)
%	->
%	write(S1, H),
%	write(S1, '.'),
%	nl(S1),
%	close(S1)
%	;	
	(functor(H,#,_) -> numbervars(H,0,_ ); numbervars(H,23,_ )),
	write_term(S1,H, [numbervars(true)]),
	write(S1, '.'),
	nl(S1),
%	close(S1)),
	write_term_to_file(S1,T).

print_models(M):-
	findall(Sub, M:model(Sub), P),
	print_list(P).

print_list([H|T]):-
	list_predicate(H,L),
	write(H), write('= '), write(L),nl,
	print_list(T).

print_list([]).

list_predicate(M1,L1):-
	findall(E,(current_predicate(M1:P/A), functor(E,P,A), M1:E),L1).


% T wrote.

print_equil([H|T]) :- 	
	findall(Sub, H:model(Sub), P),
	print_list_equil(P),	
	print_equil(T).

print_equil([]).

print_list_equil([H|_]) :-
	list_predicate(H,L), 
	write(L), write(' , ').
	

print_list_equil([]).



/*
store_retractable(Name,L):-
	on_exception(Err, retractableTMP(Name,L1), (Err = existence_error(_,_))) 
	->
	union(L,L1,L2),
	retractall(retractableTMP(Name,_)),
	asserta(retractableTMP(Name,L2))		
	;
	asserta(retractableTMP(Name,L)).
*/

%--------predicate change_parm/2: change parameter of an ASP-module
change_parm(Name,Paras):-
	retractall(parasTMP(Name,_)),
%	total_models(Name,N),
%	clear_module(Name),
%	clear_modules(Name,N,1),
	\+ clear_all_modules(Name),
	use_asp(Name,Paras).
	
create_modul(ModulName,[H|T]):-
	assert(ModulName:H),
	create_modul(ModulName,T).

create_modul(_,[]).


%----------writeASP file----------------create_asp('bridge_t','tiep2').
create_asp(Filename,OutputFile):-
	retractall(activeModule(_)),
	retractall(bridge_num(_)),
	assert(bridge_num(0)),
	assert(activeModule(Filename)),
	process(Filename,X),!,	
	split_1_char(X,'.',L),
	preprocess(L,X1),
	preprocess_remove_add_space(X1,X2),
	write_asp(X2,OutputFile,Filename).

preprocess(H,T):-
	last(H,Last),
	atom_chars(Last,List),
	delete(List,' ',Remain),
	Remain == [],
	rev(H,HRev),
	delete(HRev,Last,1,HRev1),
	rev(HRev1,H1),
	T = H1.
preprocess(H,T):-
	last(H,Last),
	atom_chars(Last,List),
	delete(List,' ',Remain),
	\+ Remain == [],
	T = H.

preprocess_remove_add_space([],[]).
preprocess_remove_add_space([H|T],[H1|T1]):-
	atom_chars(H,A),
	(append(A0, [':','-'|A1], A) -> 
		nth1(1,A1,First),
		(First == ' ' -> A2 = A1; append([[' '],A1],A2)), append(A0,[':','-'|A2],Anew);
		Anew = A),
	(append(B, [':','-'|B1], Anew) -> 
		last(B,Last),
		(Last == ' ' -> B2 = B; append([B,[' ']],B2)), append(B2,[':','-'|B1],Bnew);
		Bnew = Anew),
	atom_chars(H1,Bnew),
	preprocess_remove_add_space(T,T1).
	
    


	

	
	
% process('test1.lp',X), split_1_char(X,'.',L), write_asp(L,'tiep',F).
%
process(Filename,List) :-
	%atom_concat(File,'.lp',Filename),
        open(Filename, read, In),
        get_char(In, Char1),
        process_stream(Char1, In, List,1),!,
        close(In).

process_stream(Char, _,L,_) :-
        %print(Char),
	Char == end_of_file,
	L = [].

process_stream(Char,In,[X|L],Comment):-
	Comment == 1,	
	Char == '\n',
	get_char(In, Char2),
	X = ' ',
	process_stream(Char2, In,L,1).

process_stream(Char,In,[X|L],Comment):-
	Comment == 1,	
	Char == '\t',
	get_char(In, Char2),
	X = ' ',
	process_stream(Char2, In,L,1).

process_stream(Char,In,[X1,X2|L],Comment):-
	Comment == 1,	
	Char == ',',
	get_char(In, Char2),
	X1 = ',',
	X2 = ' ',
	process_stream(Char2, In,L,1).

%process_stream(Char,In,X):-
%	Char == ' ',
%	get_char(In, Char2),
%	process_stream(Char2, In,X).

	
        
process_stream(Char, In,[X|L],Comment) :-
        %print(Char),
	Comment == 1,		
	\+ Char == '%',	
	\+ Char == '\n',
	Char = X,
        get_char(In, Char2),	
        process_stream(Char2, In,L,1).

process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 1,	
	Char2 \== end_of_file,
	Char == '%',	
        get_char(In, Char2),	
        process_stream(Char2, In,L,2). %--start a comment or a comment block

process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 2,	
	Char2 \== end_of_file,
	Char == '*',	
        get_char(In, Char2),	
        process_stream(Char2, In,L,3). %--block comment 

process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 2,	
	Char2 \== end_of_file,
	\+ Char == '*',	
	\+ Char == '\n',
        get_char(In, Char2),	
        process_stream(Char2, In,L,5).  %--a line comment

process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 2,	
	Char2 \== end_of_file,
	\+ Char == '*',	
	Char == '\n',
        get_char(In, Char2),	
        process_stream(Char2, In,L,1).  %--a line comment

process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 5,	%--comment with %
	Char2 \== end_of_file,
	Char == '\n',	
        get_char(In, Char2),	
        process_stream(Char2, In,L,1).

process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 5,	
	Char2 \== end_of_file,
	\+ Char == '\n',	
        get_char(In, Char2),	
        process_stream(Char2, In,L,5).

process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 3,	
	Char2 \== end_of_file,
	Char == '*',
        get_char(In, Char2),	
        process_stream(Char2, In,L,4). %--might finish the block comment



process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 4,	
	Char2 \== end_of_file,
	Char == '%',
        get_char(In, Char2),	
        process_stream(Char2, In,L,1). %--finish the block comment

process_stream(Char, In,[_|L],Comment) :-
        %print(Char),
	Comment == 4,	
	Char2 \== end_of_file,
	\+ Char == '*',
        get_char(In, Char2),	
        process_stream(Char2, In,L,4).

process_stream(Char, In,[_|L],Comment) :-
        %print(Char),
	Comment == 4,	
	Char2 \== end_of_file,
	\+ Char == '%',
	\+ Char == '*',
        get_char(In, Char2),	
        process_stream(Char2, In,L,3).

process_stream(Char, In,L,Comment) :-
        %print(Char),
	Comment == 3,	
	Char2 \== end_of_file,
	\+ Char == '*',
        get_char(In, Char2),	
        process_stream(Char2, In,L,3).

%-------------------------------------------------
% split list by 1-character splitter

split_1_char(C, E, L) :-    
    split_1_chars(C, E, L).
    

split_1_chars([], _, []).

split_1_chars(C, E, [A|L]) :-
    append(C0, [E|C1], C),
    (C1 \== [] -> nth1(1,C1,Element),\+ Element == '.' ; true),
    last(C0,LastE),
    \+ LastE == '.',
    atom_chars(A, C0),
    split_1_chars(C1, E, L).

split_1_chars(C, _, [A]) :-
    atom_chars(A, C).


%-------------------------------------------------
% split list by 1-character splitter

split_2_char(C, E, L) :-    
    split_2_chars(C, E, L).

split_2_chars([], _, []).
split_2_chars(C, [E,M], [A|L]) :-
    append(C0, [E,M|C1], C), !,
    atom_chars(A, C0),
    split_2_chars(C1, [E,M], L).

split_2_chars(C, _, [A]) :-
    atom_chars(A, C).


write_asp(L,Name,Prog):-
	atom_concat(Name,'.lp',Filename),	
	open(Filename,write,Stream),
	write_asp1(L,Stream,Prog),
	make_bridge_rule(Prog,Stream),
	%make_redunt(Stream),
	close(Stream).
make_redunt(Stream):-
	X = '#hide arcg/2. #hide vertex/1. #hide is_color/1.',
	write(Stream,X),nl(Stream).

write_asp1([],_,_):-true,!.


write_asp1([H|L],Stream,Prog):-    
    atom_chars(H,List),
    %write(List),%nl,
    split_2_char(List,[':','-'],List1),
    %write(List1),%nl,
    test_br(List1,Stream,Prog),
    write_asp1(L,Stream,Prog).
    

        
test_br([H|T],Stream,Prog):-
    proper_length(T,LengthOfT),
    LengthOfT \== 1,
    concat_list([H|T],X),    
    atom_chars(X,X1), 
    remove_space(X1,X2,' ',' '),
	remove_space(X2,X21,'(','('),
	remove_space(X21,X22,'{','{'),
	remove_space(X22,X23,'}','}'),
	remove_space(X23,X24,',',','),
	remove_space2(X24,X25),
    last(Fore,Last,X25),
    (Last == ' ' -> atom_chars(X31,Fore), atom_concat(X31,'.',X3), assert(Prog:ruleLP(X31));atom_chars(X31,X25),atom_concat(X31,'.',X3),assert(Prog:ruleLP(X31))). %now is not including '.'
    %write(Stream,X), write(Stream,'.'),nl(Stream). %%this is for write to new asp file in order to change bridge rule

test_br([H|T],Stream,Prog):-
    proper_length(T,LengthOfT),
    LengthOfT == 1,
    T = [E],
    atom_chars(E,ListOfT),
    \+ member(':',ListOfT),        
    concat_list([H|T],X),   
    atom_chars(X,X1), 
    remove_space(X1,X2,' ',' '),
	remove_space(X2,X21,'(','('),
	remove_space(X21,X22,'{','{'),
	remove_space(X22,X23,'}','}'),
	remove_space(X23,X24,',',','),
	remove_space2(X24,X25),
    last(Fore,Last,X25),
    (Last == ' ' -> atom_chars(X31,Fore), atom_concat(X31,'.',X3), assert(Prog:ruleLP(X31));atom_chars(X31,X25),atom_concat(X31,'.',X3),assert(Prog:ruleLP(X31))).
    %write(Stream,X), write(Stream,'.'),nl(Stream). %%this is for write to new asp file in order to change bridge rule


test_br([H|T],Stream,Prog):-
    proper_length(T,LengthOfT),
    LengthOfT == 1,
    T = [E],
    atom_chars(E,ListOfT),
    member(':',ListOfT),
    member('{',ListOfT),    
    concat_list([H|T],X),   
    atom_chars(X,X1), 
    remove_space(X1,X2,' ',' '),
	remove_space(X2,X21,'(','('),
	remove_space(X21,X22,'{','{'),
	remove_space(X22,X23,'}','}'),
	remove_space(X23,X24,',',','),
	remove_space2(X24,X25),
    last(Fore,Last,X25),
    (Last == ' ' -> atom_chars(X31,Fore), atom_concat(X31,'.',X3), assert(Prog:ruleLP(X31));atom_chars(X31,X25),atom_concat(X31,'.',X3),assert(Prog:ruleLP(X31))).
    %write(Stream,X), write(Stream,'.'),nl(Stream). %%this is for write to new asp file in order to change bridge rule

test_br([H|T],Stream,Prog):-
    proper_length(T,LengthOfT),
    LengthOfT == 1,
    T = [E],
    atom_chars(E,ListOfT),
    member(':',ListOfT),
    \+ member('{',ListOfT),
    %nth1(Index,ListOfT,':'),
    %IndexNext is Index + 1,
    %nth1(IndexNext,ListOfT,Symbol),
    %Symbol == '=',   
    member('=',ListOfT),    
    concat_list([H|T],X),   
    atom_chars(X,X1), 
    remove_space(X1,X2,' ',' '),
	remove_space(X2,X21,'(','('),
	remove_space(X21,X22,'{','{'),
	remove_space(X22,X23,'}','}'),
	remove_space(X23,X24,',',','),
	remove_space2(X24,X25),
    last(Fore,Last,X25),
    (Last == ' ' -> atom_chars(X31,Fore), atom_concat(X31,'.',X3), assert(Prog:ruleLP(X31));atom_chars(X31,X25),atom_concat(X31,'.',X3),assert(Prog:ruleLP(X31))).
    %write(Stream,X), write(Stream,'.'),nl(Stream). %%this is for write to new asp file in order to change bridge rule

test_br([H|T],Stream,Prog):-
    proper_length(T,LengthOfT),
    LengthOfT == 1,
    T = [E],
    atom_chars(E,ListOfT),
    member(':',ListOfT),
    \+ member('{',ListOfT), 
    %nth1(Index,ListOfT,':'),
    %IndexNext is Index + 1,
    %nth1(IndexNext,ListOfT,Symbol),
    %\+ Symbol == '=',      
    \+ member('=',ListOfT),
    %write('bridge rule'), %nl,
    %write([H|T]),%nl, 
    retract(bridge_num(Nu)),
    New_Nu is Nu + 1,
    assert(bridge_num(New_Nu)),
    retract(dependency_number(Number)),  
    New_N is Number + 1,
    assert(dependency_number(New_N)), 
    atom_codes(H,Codes),
    (Codes == [32] -> H1 = 'false' , 
		%write(Stream, ':- false.'), nl(Stream),  %%this is for write to new asp file in order to change bridge rule
		assert(Prog:ruleLP(':- false')) ; H1 = H),
    make_depen([H1|T],Prog,Stream).
  

make_bridge_rule(Prog,Stream):-
	bridge_num(X),	
	\+ X == 0,
	make_bridge_rule1(Prog,Stream,X).
make_bridge_rule(_,_):-
	bridge_num(X),	
	X == 0.
make_bridge_rule1(_,_,X):-
	X == 0.
make_bridge_rule1(Prog,Stream,X):-
	\+ X == 0,
	findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E, E=dependency(Prog,_,_,_,_,X) ),List), 	
	List = [H|_],
	H = dependency(_,X1,_,_,_,_),
	%atom_concat(Prog,'___',Prog1),	
	%atom_concat(Prog1, X1, Prog2),	
	make_t_mcs(Prog,X1,Prog___X1),  	
	atom_concat(Prog___X1,' :- ', Prog3),
	create_bridge_rule(List,Prog3,Sout1),
	atom_concat(Sout1,'.',Sout),
	assert(Prog:ruleLP(Sout1)),
	%write(Stream,Sout), %write(Stream,'.'), %%this is for write to new asp file in order to change bridge rule
	%nl(Stream), %%this is for write to new asp file in order to change bridge rule
	X_new is X - 1,	
	make_bridge_rule1(Prog,Stream,X_new).


create_bridge_rule([T],Sin,Sout):-
	T = dependency(X,_,Z,W,M,_),			
	make_t_mcs(Z,W,Z___W),
	(X \== Z ->
		(M==1 -> atom_concat(Sin, Z___W,Sin1); 
			atom_concat(Sin,'not ',Sin3),atom_concat(Sin3, Z___W,Sin1)) ;
		(M==1 -> atom_concat(Sin, W ,Sin1); 
			atom_concat(Sin,'not ',Sin3),atom_concat(Sin3, W,Sin1)) ),		
	Sout = Sin1.

create_bridge_rule([H|T],Sin,Sout):-
	H = dependency(X,_,Z,W,M,_),			
	make_t_mcs(Z,W,Z___W),
	(X \== Z ->
		(M==1 -> atom_concat(Sin, Z___W,Sin1), atom_concat(Sin1, ', ',Sin2); 
			atom_concat(Sin,'not ',Sin3),atom_concat(Sin3, Z___W,Sin1), atom_concat(Sin1, ', ',Sin2)) ;
		(M==1 -> atom_concat(Sin, W,Sin1), atom_concat(Sin1, ', ',Sin2); 
			atom_concat(Sin,'not ',Sin3),atom_concat(Sin3, W,Sin1), atom_concat(Sin1, ', ',Sin2)) ),
	create_bridge_rule(T,Sin2,Sout).

	
	
remove_space([],[],_,_).
remove_space([H|T],[H1|T1], Before,RemovedMark):-
    \+ Before == RemovedMark,
    H1 = H,
    remove_space(T,T1,H,RemovedMark).
remove_space([H|T],T1,Before,RemovedMark):-
    Before == RemovedMark,
    H == ' ',
    remove_space(T,T1,' ',RemovedMark).
remove_space([H|T],[H1|T1],Before,RemovedMark):-
    Before == RemovedMark,    
    \+ H == ' ',
    H1 = H,
    remove_space(T,T1,H,RemovedMark).



%% remove_space2 removes space before ')'	 and ',' and '}'
remove_space2(I,O):-
	rev(I,RevI),
	remove_space(RevI,RevO,')',')'),
	remove_space(RevO,RevO1,',',','),
	remove_space(RevO1,RevO2,'}','}'),
	remove_space(RevO2,RevO3,'{','{'),
	rev(RevO3,O).

preprocess_remove_space(I,O):-
	atom_chars(I,X1),
	remove_space(X1,X2,' ',' '),
	remove_space(X2,X21,'(','('),
	remove_space(X21,X22,'{','{'),
	remove_space(X22,X23,'}','}'),
	remove_space(X23,X24,',',','),
	remove_space2(X24,X25),
	atom_chars(O,X25).
	

	
concat_list([T],S):-
	S = T.

concat_list([H|T],S):-
	concat_list(T,S1),
	atom_concat(':-',S1,S2),
	atom_concat(H,S2,S).
	%write(S),%nl.
%-------------------------------------------- assert and retract from a module
% assert_string_fact_to_module(Module,Fact) where Fact is a list of string representing a fact, inserting into Module:X.
assert_string_fact_to_module(ModulName,Fact):-
	open('temp_assert.pl',write,S1),
	assert_string_fact_to_module1(S1,Fact),
	close(S1),
%	open('temp_assert.pl',read,S2),
%	read_line(S2,L1),
%	(L1  \== end_of_file ->
%		read_from_codes(L1,M),
%		assert(Name:model(ModulName)),
%		asp:create_modul(ModulName,M);true),
%	close(S2),
	[temp:temp_assert],
	findall(E,(temp:current_predicate(E1/N1),functor(E,E1,N1),temp:E),LA), %%/need to create module temp because load [temp_assert] will remove previous uploaded predicates 
	asp:create_modul(ModulName,LA),
	absolute_file_name('$SHELL', Shell1),
	process_create(Shell1, ['-c', ['rm -f ', 'temp_assert.pl']], [process(P1)]),
	process_wait(P1,exit(0)).
%	read_from_stream(Stream,Name));read_from_stream(Stream,Name)).

assert_string_fact_to_module1(_,[]).
assert_string_fact_to_module1(S1,[H|T]):-
	write(S1,H),write(S1,'.\n'),
	assert_string_fact_to_module1(S1,T).
	
%% assert predicate (fact) to module
assert_fact_to_module(Module,Fact):-
	%print(Fact),nl,
	assert(Module:ruleLP(Fact)).
	
retract_fact_from_module(Module,Fact):-
	(retract(Module:ruleLP(Fact)) -> true ; print('Fact \''), print(Fact), print(' \' does not exist!')). 
	
	
% assert_to_module(Module,Rule) where Rule is a string representing a rule, inserting into Module:ruleLP(X)
%need to check if module exists or not.
assert_to_module(Module,Rule):-
	preprocess_remove_add_space([Rule],[Rule1]),
	preprocess_remove_space(Rule1,ProcessedRule),
	%atom_concat(ProcessedRule,'.',ProcessedRule1),
	assert(Module:ruleLP(ProcessedRule)).
	
retract_from_module(Module,Rule):-
	preprocess_remove_add_space([Rule],[Rule1]),
	preprocess_remove_space(Rule1,ProcessedRule),
	%atom_concat(ProcessedRule,'.',ProcessedRule1),
	(retract(Module:ruleLP(ProcessedRule)) -> true ; print('Rule \''), print(ProcessedRule), print(' \' does not exist!')). 
%-----------------------------------------------------	
split_1_char_br(C, E, L) :-    
    split_1_chars_br(C, E, L).
    

split_1_chars_br([], _, []).

split_1_chars_br(C, E, [A|L]) :-
    append(C0, [E|C1], C),
    count_appear(C0,'(',N),
    count_appear(C0, ')',N),    
    atom_chars(A, C0),
    split_1_chars_br(C1, E, L).

split_1_chars_br(C, _, [A]) :-
    atom_chars(A, C).

count_appear([],_,0).
	
count_appear([H|T],C,O):-
	count_appear(T,C,O1),
	(H==C -> O is O1 + 1; O = O1).
%------------------------------------------------------

make_depen([H|T],Prog,Stream):-
	T=[T1],
	atom_chars(T1,N1),
    	%write('remove braket'), %nl,	
	split_1_char_br(N1,',',List1),
	make_depen1(H,Prog,List1,Stream).



delete_last(N21,C,O21):-
	rev(N21,N12),
	delete(N12,C,1,O12),
	rev(O12,O21).
concat_bridge_rule([T],T,_).
concat_bridge_rule([H|T],Output,C):-
	append([H,[C]],H1),
	concat_bridge_rule(T,Out),
	append([H1,Out],Output).

make_depen1(_,_,[],_).
make_depen1(H,Prog,[T|L],Stream):-
	atom_chars(T,List1),
	delete(List1,'(',1,List2),
	delete_last(List2,')',List),	
	\+ subseq(List,[n,o,t,' '], _),
	split_1_char(List,':',ListNew),
	ListNew = [A,B],
	atom_chars(H,ListH),
	delete(ListH,' ',ListHAfter),
	atom_chars(H1, ListHAfter),
	atom_chars(A,ListA),
	delete(ListA,' ',ListAAfter),
	append(['p'],ListAAfter,ListAAfter1),
	atom_chars(A1, ListAAfter1),
	atom_chars(B,ListB),
	delete(ListB,' ',ListBAfter),
	atom_chars(B1, ListBAfter),
	dependency_number(Number),
	make_t_mcs(A1,B1,Temp),
	%Temp=..['t_mcs',A1,B1],	
	Term=..['dependency',Prog,H1,A1,B1,1,Number],
	%write('ko n '), %print(Term), %nl,
	assert(Term),
	%atom_concat(Prog,'___', NewProg1),
	%atom_concat(NewProg1,H1,NewProg2),
	%atom_concat(A1, '___', A2),
	%atom_concat(A2,B1,A3),
	(Prog \== A1 ->	
		atom_concat('0{ ', Temp, F1),
		atom_concat(F1, ' }1.',F2),
		write(Stream,F2),
		%write(Stream,'.'),
		nl(Stream),
		assert(Prog:ruleLP(F2)) ; 
		true),
		atom_concat(H1,' :- ', F3),
		make_t_mcs(Prog, H1, NewProg2),
		atom_concat(F3, NewProg2,F41),
		atom_concat(F41,'.',F4),
		write(Stream,F4),
		%write(Stream,'.'),
		nl(Stream),
		assert(Prog:ruleLP(F4)),		
	make_depen1(H,Prog,L,Stream).
	
make_depen1(H,Prog,[T|L],Stream):-
	atom_chars(T,List1),
	delete(List1,'(',1,List2),
	delete_last(List2,')',List),	
	subseq(List,[n,o,t,' '], X),
	split_1_char(X,':',List_new),
	List_new = [A,B],
	atom_chars(H,ListH),      %--- /*--too remove all spaces  */
	delete(ListH,' ',ListHAfter), 
	atom_chars(H1, ListHAfter),
	atom_chars(A,ListA),
	delete(ListA,' ',ListAAfter),
	append(['p'],ListAAfter,ListAAfter1),
	atom_chars(A1, ListAAfter1),
	atom_chars(B,ListB),
	delete(ListB,' ',ListBAfter),
	atom_chars(B1, ListBAfter),
	dependency_number(Number),	
	make_t_mcs(A1,B1,Temp),
	%Temp=..['t_mcs',A1,B1],
	Term=..['dependency',Prog,H1,A1,B1,2,Number],	
	%write('not '), %print(Term), %nl,
	assert(Term),
	%atom_concat(Prog,'___', NewProg1),
	%atom_concat(NewProg1,H1,NewProg2),
	%atom_concat(A1, '___', A2),
	%atom_concat(A2,B1,A3),
	(Prog \== A1 -> 	
		atom_concat('0{ ', Temp, F1),
		atom_concat(F1, ' }1',F2),
		write(Stream,F2),write(Stream,'.'),nl(Stream),
		assert(Prog:F2) ; 
		true),
		atom_concat(H1,' :- ', F3),
		make_t_mcs(Prog, H1, NewProg2),
		atom_concat(F3, NewProg2,F4),
		write(Stream,F4),write(Stream,'.'),nl(Stream),
		assert(Prog:F4),		
	make_depen1(H,Prog,L,Stream).

	
make_t_mcs(A1,B1,Out):-
	atom_concat('t_mcs(', A1 , New),
	atom_concat(New, ',' , New1),
	atom_concat(New1, B1, New2),
	atom_concat(New2, ')', Out).



%------------------------------------------------------------------------------
%------------------to print running time
print_statistics(T_elapsed):-   
    nl, nl,        
    write('runtime_'),
    write(T_elapsed), write('msec.'), nl.
     

%--------use_asp_equil: load models of file Name into List,store them in models_asp(Name,List). T wrote.

remove_set1([],[]).
remove_set1([H|T],[H1|T1]):-
	atom_chars(H,Chars),
	Chars = [Head|_],
	Head == 'c',
	H1 = H,
	remove_set1(T,T1).
remove_set1([H|T],T1):-
	atom_chars(H,Chars),
	Chars = [Head|_],
	\+ Head == 'c',	
	remove_set1(T,T1).

remove_set2(X,X1):-
	keys_and_values(X,H,T),
	remove_set3(T,T1),
	keys_and_values(X1,H,T1).

remove_set3([],[]).
remove_set3([H|T],[H1|T1]):-
	remove_set1(H,H1),
	remove_set3(T,T1).

tiep:-
	statistics(walltime,[T_elapsed1,_]),	
	use_asp_equil1([p1,p2,p3,p4,p5,p6,p7,p8,p9,p10]),
%,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115,p116,p117,p118,p119,p120,p121,p122,p123,p124,p125,p126,p127,p128,p129,p130,p131,p132,p133,p134,p135,p136,p137,p138,p139,p140,p141,p142,p143,p144,p145,p146,p147,p148,p149,p150,p151,p152,p153,p154,p155,p156,p157,p158,p159,p160,p161,p162,p163,p164,p165,p166,p167,p168,p169,p170,p171,p172,p173,p174,p175,p176,p177,p178,p179,p180,p181,p182,p183,p184,p185,p186,p187,p188,p189,p190,p191,p192,p193,p194,p195,p196,p197,p198,p199,p200,p201,p202,p203,p204,p205,p206,p207,p208,p209,p210,p211,p212,p213,p214,p215,p216,p217,p218,p219,p220,p221,p222,p223,p224,p225,p226,p227,p228,p229,p230,p231,p232,p233,p234,p235,p236,p237,p238,p239,p240,p241,p242,p243,p244,p245,p246,p247,p248,p249,p250,p251,p252,p253,p254,p255,p256,p257,p258,p259,p260,p261,p262,p263,p264,p265,p266,p267,p268,p269,p270,p271,p272,p273,p274,p275,p276,p277,p278,p279,p280,p281,p282,p283,p284,p285,p286,p287,p288,p289,p290,p291,p292,p293,p294,p295,p296,p297,p298,p299,p300,p301,p302,p303,p304,p305,p306,p307,p308,p309,p310,p311,p312,p313,p314,p315,p316,p317,p318,p319,p320,p321,p322,p323,p324,p325,p326,p327,p328,p329,p330,p331,p332,p333,p334,p335,p336,p337,p338,p339,p340,p341,p342,p343,p344,p345,p346,p347,p348,p349,p350,p351,p352,p353,p354,p355,p356,p357,p358,p359,p360,p361,p362,p363,p364,p365,p366,p367,p368,p369,p370,p371,p372,p373,p374,p375,p376,p377,p378,p379,p380,p381,p382,p383,p384,p385,p386,p387,p388,p389,p390,p391,p392,p393,p394,p395,p396,p397,p398,p399,p400]),

%,p401,p402,p403,p404,p405,p406,p407,p408,p409,p410,p411,p412,p413,p414,p415,p416,p417,p418,p419,p420,p421,p422,p423,p424,p425,p426,p427,p428,p429,p430,p431,p432,p433,p434,p435,p436,p437,p438,p439,p440,p441,p442,p443,p444,p445,p446,p447,p448,p449,p450,p451,p452,p453,p454,p455,p456,p457,p458,p459,p460,p461,p462,p463,p464,p465,p466,p467,p468,p469,p470,p471,p472,p473,p474,p475,p476,p477,p478,p479,p480,p481,p482,p483,p484,p485,p486,p487,p488,p489,p490,p491,p492,p493,p494,p495,p496,p497,p498,p499,p500,p501,p502,p503,p504,p505,p506,p507,p508,p509,p510,p511,p512,p513,p514,p515,p516,p517,p518,p519,p520,p521,p522,p523,p524,p525,p526,p527,p528,p529,p530,p531,p532,p533,p534,p535,p536,p537,p538,p539,p540,p541,p542,p543,p544,p545,p546,p547,p548,p549,p550,p551,p552,p553,p554,p555,p556,p557,p558,p559,p560,p561,p562,p563,p564,p565,p566,p567,p568,p569,p570,p571,p572,p573,p574,p575,p576,p577,p578,p579,p580,p581,p582,p583,p584,p585,p586,p587,p588,p589,p590,p591,p592,p593,p594,p595,p596,p597,p598,p599,p600,p601,p602,p603,p604,p605,p606,p607,p608,p609,p610,p611,p612,p613,p614,p615,p616,p617,p618,p619,p620,p621,p622,p623,p624,p625,p626,p627,p628,p629,p630,p631,p632,p633,p634,p635,p636,p637,p638,p639,p640,p641,p642,p643,p644,p645,p646,p647,p648,p649,p650,p651,p652,p653,p654,p655,p656,p657,p658,p659,p660,p661,p662,p663,p664,p665,p666,p667,p668,p669,p670,p671,p672,p673,p674,p675,p676,p677,p678,p679,p680,p681,p682,p683,p684,p685,p686,p687,p688,p689,p690,p691,p692,p693,p694,p695,p696,p697,p698,p699,p700,p701,p702,p703,p704,p705,p706,p707,p708,p709,p710,p711,p712,p713,p714,p715,p716,p717,p718,p719,p720,p721,p722,p723,p724,p725,p726,p727,p728,p729,p730,p731,p732,p733,p734,p735,p736,p737,p738,p739,p740,p741,p742,p743,p744,p745,p746,p747,p748,p749,p750,p751,p752,p753,p754,p755,p756,p757,p758,p759,p760,p761,p762,p763,p764,p765,p766,p767,p768,p769,p770,p771,p772,p773,p774,p775,p776,p777,p778,p779,p780,p781,p782,p783,p784,p785,p786,p787,p788,p789,p790,p791,p792,p793,p794,p795,p796,p797,p798,p799,p800,p801,p802,p803,p804,p805,p806,p807,p808,p809,p810,p811,p812,p813,p814,p815,p816,p817,p818,p819,p820,p821,p822,p823,p824,p825,p826,p827,p828,p829,p830,p831,p832,p833,p834,p835,p836,p837]),
	%use_asp_equil1([p838,p839,p840,p841,p842,p843,p844,p845,p846,p847,p848,p849,p850,p851,p852,p853,p854,p855,p856,p857,p858,p859,p860,p861,p862,p863,p864,p865,p866,p867,p868,p869,p870,p871,p872,p873,p874,p875,p876,p877,p878,p879,p880,p881,p882,p883,p884,p885,p886,p887,p888,p889,p890,p891,p892,p893,p894,p895,p896,p897,p898,p899,p900,p901,p902,p903,p904,p905,p906,p907,p908,p909,p910,p911,p912,p913,p914,p915,p916,p917,p918,p919,p920,p921,p922,p923,p924,p925,p926,p927,p928,p929,p930,p931,p932,p933,p934,p935,p936,p937,p938,p939,p940,p941,p942,p943,p944,p945,p946,p947,p948,p949,p950,p951,p952,p953,p954,p955,p956,p957,p958,p959,p960,p961,p962,p963,p964,p965,p966,p967,p968,p969,p970,p971,p972,p973,p974,p975,p976,p977,p978,p979,p980,p981,p982,p983,p984,p985,p986,p987,p988,p989,p990,p991,p992,p993,p994,p995,p996,p997,p998,p999,p1000,p1001,p1002,p1003,p1004,p1005,p1006,p1007,p1008,p1009,p1010,p1011,p1012,p1013,p1014,p1015,p1016,p1017,p1018,p1019,p1020,p1021,p1022,p1023,p1024,p1025,p1026,p1027,p1028,p1029,p1030,p1031,p1032,p1033,p1034,p1035,p1036,p1037,p1038,p1039,p1040,p1041,p1042,p1043,p1044,p1045,p1046,p1047,p1048,p1049,p1050,p1051,p1052,p1053,p1054,p1055,p1056,p1057,p1058,p1059,p1060,p1061,p1062,p1063,p1064,p1065,p1066,p1067,p1068,p1069,p1070,p1071,p1072,p1073,p1074,p1075,p1076,p1077,p1078,p1079,p1080,p1081,p1082,p1083,p1084,p1085,p1086,p1087,p1088,p1089,p1090,p1091,p1092,p1093,p1094,p1095,p1096,p1097,p1098,p1099,p1100,p1101,p1102,p1103,p1104,p1105,p1106,p1107,p1108,p1109,p1110,p1111,p1112,p1113,p1114,p1115,p1116,p1117,p1118,p1119,p1120,p1121,p1122,p1123,p1124,p1125,p1126,p1127,p1128,p1129,p1130,p1131,p1132,p1133,p1134,p1135,p1136,p1137,p1138,p1139,p1140,p1141,p1142,p1143,p1144,p1145,p1146,p1147,p1148,p1149,p1150,p1151,p1152,p1153,p1154,p1155,p1156,p1157,p1158,p1159,p1160,p1161,p1162,p1163,p1164,p1165,p1166,p1167,p1168,p1169,p1170,p1171,p1172,p1173,p1174,p1175,p1176,p1177,p1178,p1179,p1180,p1181,p1182,p1183,p1184,p1185,p1186,p1187,p1188,p1189,p1190,p1191,p1192,p1193,p1194,p1195,p1196,p1197,p1198,p1199,p1200,p1201,p1202,p1203,p1204,p1205,p1206,p1207,p1208,p1209,p1210,p1211,p1212,p1213,p1214,p1215,p1216,p1217,p1218,p1219,p1220,p1221,p1222,p1223,p1224,p1225,p1226,p1227,p1228,p1229,p1230,p1231,p1232,p1233,p1234,p1235,p1236,p1237,p1238,p1239,p1240,p1241,p1242,p1243,p1244,p1245,p1246,p1247,p1248,p1249,p1250,p1251,p1252,p1253,p1254,p1255,p1256,p1257,p1258,p1259,p1260,p1261,p1262,p1263,p1264,p1265,p1266,p1267,p1268,p1269,p1270,p1271,p1272,p1273,p1274,p1275,p1276,p1277,p1278,p1279,p1280,p1281,p1282,p1283,p1284,p1285,p1286,p1287,p1288,p1289,p1290,p1291,p1292,p1293,p1294,p1295,p1296,p1297,p1298,p1299,p1300,p1301,p1302,p1303,p1304,p1305,p1306,p1307,p1308,p1309,p1310,p1311,p1312,p1313,p1314,p1315,p1316,p1317,p1318,p1319,p1320,p1321,p1322,p1323,p1324,p1325,p1326,p1327,p1328,p1329,p1330,p1331,p1332,p1333,p1334,p1335,p1336,p1337,p1338,p1339,p1340,p1341,p1342,p1343,p1344,p1345,p1346,p1347,p1348,p1349,p1350,p1351,p1352,p1353,p1354,p1355,p1356,p1357,p1358,p1359,p1360,p1361,p1362,p1363,p1364,p1365,p1366,p1367,p1368,p1369,p1370,p1371,p1372,p1373,p1374,p1375,p1376,p1377,p1378,p1379,p1380,p1381,p1382,p1383,p1384,p1385,p1386,p1387,p1388,p1389,p1390,p1391,p1392,p1393,p1394,p1395,p1396,p1397,p1398,p1399,p1400,p1401,p1402,p1403,p1404,p1405,p1406,p1407,p1408,p1409,p1410,p1411,p1412,p1413,p1414,p1415,p1416,p1417,p1418,p1419,p1420,p1421,p1422,p1423,p1424,p1425,p1426,p1427,p1428,p1429,p1430,p1431,p1432,p1433,p1434,p1435,p1436,p1437,p1438,p1439,p1440,p1441,p1442,p1443,p1444,p1445,p1446,p1447,p1448,p1449,p1450,p1451,p1452,p1453,p1454,p1455,p1456,p1457,p1458,p1459,p1460,p1461,p1462,p1463,p1464,p1465,p1466,p1467,p1468,p1469,p1470,p1471,p1472,p1473,p1474,p1475,p1476,p1477,p1478,p1479,p1480,p1481,p1482,p1483,p1484,p1485,p1486,p1487,p1488,p1489,p1490,p1491,p1492,p1493,p1494,p1495,p1496,p1497,p1498,p1499,p1500]),
	%use_asp_equil1([p1501,p1502,p1503,p1504,p1505,p1506,p1507,p1508,p1509,p1510,p1511,p1512,p1513,p1514,p1515,p1516,p1517,p1518,p1519,p1520,p1521,p1522,p1523,p1524,p1525,p1526,p1527,p1528,p1529,p1530,p1531,p1532,p1533,p1534,p1535,p1536,p1537,p1538,p1539,p1540,p1541,p1542,p1543,p1544,p1545,p1546,p1547,p1548,p1549,p1550,p1551,p1552,p1553,p1554,p1555,p1556,p1557,p1558,p1559,p1560,p1561,p1562,p1563,p1564,p1565,p1566,p1567,p1568,p1569,p1570,p1571,p1572,p1573,p1574,p1575,p1576,p1577,p1578,p1579,p1580,p1581,p1582,p1583,p1584,p1585,p1586,p1587,p1588,p1589,p1590,p1591,p1592,p1593,p1594,p1595,p1596,p1597,p1598,p1599,p1600,p1601,p1602,p1603,p1604,p1605,p1606,p1607,p1608,p1609,p1610,p1611,p1612,p1613,p1614,p1615,p1616,p1617,p1618,p1619,p1620,p1621,p1622,p1623,p1624,p1625,p1626,p1627,p1628,p1629,p1630,p1631,p1632,p1633,p1634,p1635,p1636,p1637,p1638,p1639,p1640,p1641,p1642,p1643,p1644,p1645,p1646,p1647,p1648,p1649,p1650,p1651,p1652,p1653,p1654,p1655,p1656,p1657,p1658,p1659,p1660,p1661,p1662,p1663,p1664,p1665,p1666,p1667,p1668,p1669,p1670,p1671,p1672,p1673,p1674,p1675,p1676,p1677,p1678,p1679,p1680,p1681,p1682,p1683,p1684,p1685,p1686,p1687,p1688,p1689,p1690,p1691,p1692,p1693,p1694,p1695,p1696,p1697,p1698,p1699,p1700,p1701,p1702,p1703,p1704,p1705,p1706,p1707,p1708,p1709,p1710,p1711,p1712,p1713,p1714,p1715,p1716,p1717,p1718,p1719,p1720,p1721,p1722,p1723,p1724,p1725,p1726,p1727,p1728,p1729,p1730,p1731,p1732,p1733,p1734,p1735,p1736,p1737,p1738,p1739,p1740,p1741,p1742,p1743,p1744,p1745,p1746,p1747,p1748,p1749,p1750,p1751,p1752,p1753,p1754,p1755,p1756,p1757,p1758,p1759,p1760,p1761,p1762,p1763,p1764,p1765,p1766,p1767,p1768,p1769,p1770,p1771,p1772,p1773,p1774,p1775,p1776,p1777,p1778,p1779,p1780,p1781,p1782,p1783,p1784,p1785,p1786,p1787,p1788,p1789,p1790,p1791,p1792,p1793,p1794,p1795,p1796,p1797,p1798,p1799,p1800,p1801,p1802,p1803,p1804,p1805,p1806,p1807,p1808,p1809,p1810,p1811,p1812,p1813,p1814,p1815,p1816,p1817,p1818,p1819,p1820,p1821,p1822,p1823,p1824,p1825,p1826,p1827,p1828,p1829,p1830,p1831,p1832,p1833,p1834,p1835,p1836,p1837,p1838,p1839,p1840,p1841,p1842,p1843,p1844,p1845,p1846,p1847,p1848,p1849,p1850,p1851,p1852,p1853,p1854,p1855,p1856,p1857,p1858,p1859,p1860,p1861,p1862,p1863,p1864,p1865,p1866,p1867,p1868,p1869,p1870,p1871,p1872,p1873,p1874,p1875,p1876,p1877,p1878,p1879,p1880,p1881,p1882,p1883,p1884,p1885,p1886,p1887,p1888,p1889,p1890,p1891,p1892,p1893,p1894,p1895,p1896,p1897,p1898,p1899,p1900,p1901,p1902,p1903,p1904,p1905,p1906,p1907,p1908,p1909,p1910,p1911,p1912,p1913,p1914,p1915,p1916,p1917,p1918,p1919,p1920,p1921,p1922,p1923,p1924,p1925,p1926,p1927,p1928,p1929,p1930,p1931,p1932,p1933,p1934,p1935,p1936,p1937,p1938,p1939,p1940,p1941,p1942,p1943,p1944,p1945,p1946,p1947,p1948,p1949,p1950,p1951,p1952,p1953,p1954,p1955,p1956,p1957,p1958,p1959,p1960,p1961,p1962,p1963,p1964,p1965,p1966,p1967,p1968,p1969,p1970,p1971,p1972,p1973,p1974,p1975,p1976,p1977,p1978,p1979,p1980,p1981,p1982,p1983,p1984,p1985,p1986,p1987,p1988,p1989,p1990,p1991,p1992,p1993,p1994,p1995,p1996,p1997,p1998,p1999,p2000,p2001,p2002,p2003,p2004,p2005,p2006,p2007,p2008,p2009,p2010,p2011,p2012,p2013,p2014,p2015,p2016,p2017,p2018,p2019,p2020,p2021,p2022,p2023,p2024,p2025,p2026,p2027,p2028,p2029,p2030,p2031,p2032,p2033,p2034,p2035,p2036,p2037,p2038,p2039,p2040,p2041,p2042,p2043,p2044,p2045,p2046,p2047,p2048,p2049,p2050,p2051,p2052,p2053,p2054,p2055,p2056,p2057,p2058,p2059,p2060,p2061,p2062,p2063,p2064,p2065,p2066,p2067,p2068,p2069,p2070,p2071,p2072,p2073,p2074,p2075,p2076,p2077,p2078,p2079,p2080,p2081,p2082,p2083,p2084,p2085,p2086,p2087,p2088,p2089,p2090,p2091,p2092,p2093,p2094,p2095,p2096,p2097,p2098,p2099,p2100,p2101,p2102,p2103,p2104,p2105,p2106,p2107,p2108,p2109,p2110,p2111,p2112,p2113,p2114,p2115,p2116,p2117,p2118,p2119,p2120,p2121,p2122,p2123,p2124,p2125,p2126,p2127,p2128,p2129,p2130,p2131,p2132,p2133,p2134,p2135,p2136,p2137,p2138,p2139,p2140,p2141,p2142,p2143,p2144,p2145,p2146,p2147,p2148,p2149,p2150,p2151,p2152,p2153,p2154,p2155,p2156,p2157,p2158,p2159,p2160,p2161,p2162,p2163,p2164,p2165,p2166,p2167,p2168,p2169,p2170,p2171,p2172,p2173,p2174,p2175,p2176,p2177,p2178,p2179]),
	%use_asp_equil1([p2180,p2181,p2182,p2183,p2184,p2185,p2186,p2187,p2188,p2189,p2190,p2191,p2192,p2193,p2194,p2195,p2196,p2197,p2198,p2199,p2200,p2201,p2202,p2203,p2204,p2205,p2206,p2207,p2208,p2209,p2210,p2211,p2212,p2213,p2214,p2215,p2216,p2217,p2218,p2219,p2220,p2221,p2222,p2223,p2224,p2225,p2226,p2227,p2228,p2229,p2230,p2231,p2232,p2233,p2234,p2235,p2236,p2237,p2238,p2239,p2240,p2241,p2242,p2243,p2244,p2245,p2246,p2247,p2248,p2249,p2250,p2251,p2252,p2253,p2254,p2255,p2256,p2257,p2258,p2259,p2260,p2261,p2262,p2263,p2264,p2265,p2266,p2267,p2268,p2269,p2270,p2271,p2272,p2273,p2274,p2275,p2276,p2277,p2278,p2279,p2280,p2281,p2282,p2283,p2284,p2285,p2286,p2287,p2288,p2289,p2290,p2291,p2292,p2293,p2294,p2295,p2296,p2297,p2298,p2299,p2300,p2301,p2302,p2303,p2304,p2305,p2306,p2307,p2308,p2309,p2310,p2311,p2312,p2313,p2314,p2315,p2316,p2317,p2318,p2319,p2320,p2321,p2322,p2323,p2324,p2325,p2326,p2327,p2328,p2329,p2330,p2331,p2332,p2333,p2334,p2335,p2336,p2337,p2338,p2339,p2340,p2341,p2342,p2343,p2344,p2345,p2346,p2347,p2348,p2349,p2350,p2351,p2352,p2353,p2354,p2355,p2356,p2357,p2358,p2359,p2360,p2361,p2362,p2363,p2364,p2365,p2366,p2367,p2368,p2369,p2370,p2371,p2372,p2373,p2374,p2375,p2376,p2377,p2378,p2379,p2380,p2381,p2382,p2383,p2384,p2385,p2386,p2387,p2388,p2389,p2390,p2391,p2392,p2393,p2394,p2395,p2396,p2397,p2398,p2399,p2400,p2401,p2402,p2403,p2404,p2405,p2406,p2407,p2408,p2409,p2410,p2411,p2412,p2413,p2414,p2415,p2416,p2417,p2418,p2419,p2420,p2421,p2422,p2423,p2424,p2425,p2426,p2427,p2428,p2429,p2430,p2431,p2432,p2433,p2434,p2435,p2436,p2437,p2438,p2439,p2440,p2441,p2442,p2443,p2444,p2445,p2446,p2447,p2448,p2449,p2450,p2451,p2452,p2453,p2454,p2455,p2456,p2457,p2458,p2459,p2460,p2461,p2462,p2463,p2464,p2465,p2466,p2467,p2468,p2469,p2470,p2471,p2472,p2473,p2474,p2475,p2476,p2477,p2478,p2479,p2480,p2481,p2482,p2483,p2484,p2485,p2486,p2487,p2488,p2489,p2490,p2491,p2492,p2493,p2494,p2495,p2496,p2497,p2498,p2499,p2500]),
	%use_asp_equil1([p2501,p2502,p2503,p2504,p2505,p2506,p2507,p2508,p2509,p2510,p2511,p2512,p2513,p2514,p2515,p2516,p2517,p2518,p2519,p2520,p2521,p2522,p2523,p2524,p2525,p2526,p2527,p2528,p2529,p2530,p2531,p2532,p2533,p2534,p2535,p2536,p2537,p2538,p2539,p2540,p2541,p2542,p2543,p2544,p2545,p2546,p2547,p2548,p2549,p2550,p2551,p2552,p2553,p2554,p2555,p2556,p2557,p2558,p2559,p2560,p2561,p2562,p2563,p2564,p2565,p2566,p2567,p2568,p2569,p2570,p2571,p2572,p2573,p2574,p2575,p2576,p2577,p2578,p2579,p2580,p2581,p2582,p2583,p2584,p2585,p2586,p2587,p2588,p2589,p2590,p2591,p2592,p2593,p2594,p2595,p2596,p2597,p2598,p2599,p2600,p2601,p2602,p2603,p2604,p2605,p2606,p2607,p2608,p2609,p2610,p2611,p2612,p2613,p2614,p2615,p2616,p2617,p2618,p2619,p2620,p2621,p2622,p2623,p2624,p2625,p2626,p2627,p2628,p2629,p2630,p2631,p2632,p2633,p2634,p2635,p2636,p2637,p2638,p2639,p2640,p2641,p2642,p2643,p2644,p2645,p2646,p2647,p2648,p2649,p2650,p2651,p2652,p2653,p2654,p2655,p2656,p2657,p2658,p2659,p2660,p2661,p2662,p2663,p2664,p2665,p2666,p2667,p2668,p2669,p2670,p2671,p2672,p2673,p2674,p2675,p2676,p2677,p2678,p2679,p2680,p2681,p2682,p2683,p2684,p2685,p2686,p2687,p2688,p2689,p2690,p2691,p2692,p2693,p2694,p2695,p2696,p2697,p2698,p2699,p2700,p2701,p2702,p2703,p2704,p2705,p2706,p2707,p2708,p2709,p2710,p2711,p2712,p2713,p2714,p2715,p2716,p2717,p2718,p2719,p2720,p2721,p2722,p2723,p2724,p2725,p2726,p2727,p2728,p2729,p2730,p2731,p2732,p2733,p2734,p2735,p2736,p2737,p2738,p2739,p2740,p2741,p2742,p2743,p2744,p2745,p2746,p2747,p2748,p2749,p2750,p2751,p2752,p2753,p2754,p2755,p2756,p2757,p2758,p2759,p2760,p2761,p2762,p2763,p2764,p2765,p2766,p2767,p2768,p2769,p2770,p2771,p2772,p2773,p2774,p2775,p2776,p2777,p2778,p2779,p2780,p2781,p2782,p2783,p2784,p2785,p2786,p2787,p2788,p2789,p2790,p2791,p2792,p2793,p2794,p2795,p2796,p2797,p2798,p2799,p2800,p2801,p2802,p2803,p2804,p2805,p2806,p2807,p2808,p2809,p2810,p2811,p2812,p2813,p2814,p2815,p2816,p2817,p2818,p2819,p2820,p2821,p2822,p2823,p2824,p2825,p2826,p2827,p2828,p2829,p2830,p2831,p2832,p2833,p2834,p2835,p2836,p2837,p2838,p2839,p2840,p2841,p2842,p2843,p2844,p2845,p2846,p2847,p2848,p2849,p2850,p2851,p2852,p2853,p2854,p2855,p2856,p2857,p2858,p2859,p2860,p2861,p2862,p2863,p2864,p2865,p2866,p2867,p2868,p2869,p2870,p2871,p2872,p2873,p2874,p2875,p2876,p2877,p2878,p2879,p2880,p2881,p2882,p2883,p2884,p2885,p2886,p2887,p2888,p2889,p2890,p2891,p2892,p2893,p2894,p2895,p2896,p2897,p2898,p2899,p2900,p2901,p2902,p2903,p2904,p2905,p2906,p2907,p2908,p2909,p2910,p2911,p2912,p2913,p2914,p2915,p2916,p2917,p2918,p2919,p2920,p2921,p2922,p2923,p2924,p2925,p2926,p2927,p2928,p2929,p2930,p2931,p2932,p2933,p2934,p2935,p2936,p2937,p2938,p2939,p2940,p2941,p2942,p2943,p2944,p2945,p2946,p2947,p2948,p2949,p2950,p2951,p2952,p2953,p2954,p2955,p2956,p2957,p2958,p2959,p2960,p2961,p2962,p2963,p2964,p2965,p2966,p2967,p2968,p2969,p2970,p2971,p2972,p2973,p2974,p2975,p2976,p2977,p2978,p2979,p2980,p2981,p2982,p2983,p2984,p2985,p2986,p2987,p2988,p2989,p2990,p2991,p2992,p2993,p2994,p2995,p2996,p2997,p2998,p2999,p3000]),
	%use_asp_equil1([p3001,p3002,p3003,p3004,p3005,p3006,p3007,p3008,p3009,p3010,p3011,p3012,p3013,p3014,p3015,p3016,p3017,p3018,p3019,p3020,p3021,p3022,p3023,p3024,p3025,p3026,p3027,p3028,p3029,p3030,p3031,p3032,p3033,p3034,p3035,p3036,p3037,p3038,p3039,p3040,p3041,p3042,p3043,p3044,p3045,p3046,p3047,p3048,p3049,p3050,p3051,p3052,p3053,p3054,p3055,p3056,p3057,p3058,p3059,p3060,p3061,p3062,p3063,p3064,p3065,p3066,p3067,p3068,p3069,p3070,p3071,p3072,p3073,p3074,p3075,p3076,p3077,p3078,p3079,p3080,p3081,p3082,p3083,p3084,p3085,p3086,p3087,p3088,p3089,p3090,p3091,p3092,p3093,p3094,p3095,p3096,p3097,p3098,p3099,p3100,p3101,p3102,p3103,p3104,p3105,p3106,p3107,p3108,p3109,p3110,p3111,p3112,p3113,p3114,p3115,p3116,p3117,p3118,p3119,p3120,p3121,p3122,p3123,p3124,p3125,p3126,p3127,p3128,p3129,p3130,p3131,p3132,p3133,p3134,p3135,p3136,p3137,p3138,p3139,p3140,p3141,p3142,p3143,p3144,p3145,p3146,p3147,p3148,p3149,p3150,p3151,p3152,p3153,p3154,p3155,p3156,p3157,p3158,p3159,p3160,p3161,p3162,p3163,p3164,p3165,p3166,p3167,p3168,p3169,p3170,p3171,p3172,p3173,p3174,p3175,p3176,p3177,p3178,p3179,p3180,p3181,p3182,p3183,p3184,p3185,p3186,p3187,p3188,p3189,p3190,p3191,p3192,p3193,p3194,p3195,p3196,p3197,p3198,p3199,p3200,p3201,p3202,p3203,p3204,p3205,p3206,p3207,p3208,p3209,p3210,p3211,p3212,p3213,p3214,p3215,p3216,p3217,p3218,p3219,p3220,p3221,p3222,p3223,p3224,p3225,p3226,p3227,p3228,p3229,p3230,p3231,p3232,p3233,p3234,p3235,p3236,p3237,p3238,p3239,p3240,p3241,p3242,p3243,p3244,p3245,p3246,p3247,p3248,p3249,p3250,p3251,p3252,p3253,p3254,p3255,p3256,p3257,p3258,p3259,p3260,p3261,p3262,p3263,p3264,p3265,p3266,p3267,p3268,p3269,p3270,p3271,p3272,p3273,p3274,p3275,p3276,p3277,p3278,p3279,p3280,p3281,p3282,p3283,p3284,p3285,p3286,p3287,p3288,p3289,p3290,p3291,p3292,p3293,p3294,p3295,p3296,p3297,p3298,p3299,p3300,p3301,p3302,p3303,p3304,p3305,p3306,p3307,p3308,p3309,p3310,p3311,p3312,p3313,p3314,p3315,p3316,p3317,p3318,p3319,p3320,p3321,p3322,p3323,p3324,p3325,p3326,p3327,p3328,p3329,p3330,p3331,p3332,p3333,p3334,p3335,p3336,p3337,p3338,p3339,p3340,p3341,p3342,p3343,p3344,p3345,p3346,p3347,p3348,p3349,p3350,p3351,p3352,p3353,p3354,p3355,p3356,p3357,p3358,p3359,p3360,p3361,p3362,p3363,p3364,p3365,p3366,p3367,p3368,p3369,p3370,p3371,p3372,p3373,p3374,p3375,p3376,p3377,p3378,p3379,p3380,p3381,p3382,p3383,p3384,p3385,p3386,p3387,p3388,p3389,p3390,p3391,p3392,p3393,p3394,p3395,p3396,p3397,p3398,p3399,p3400,p3401,p3402,p3403,p3404,p3405,p3406,p3407,p3408,p3409,p3410,p3411,p3412,p3413,p3414,p3415,p3416,p3417,p3418,p3419,p3420,p3421,p3422,p3423,p3424,p3425,p3426,p3427,p3428,p3429,p3430,p3431,p3432,p3433,p3434,p3435,p3436,p3437,p3438,p3439,p3440,p3441,p3442,p3443,p3444,p3445,p3446,p3447,p3448,p3449,p3450,p3451,p3452,p3453,p3454,p3455,p3456,p3457,p3458,p3459,p3460,p3461,p3462,p3463,p3464,p3465,p3466,p3467,p3468,p3469,p3470,p3471,p3472,p3473,p3474,p3475,p3476,p3477,p3478,p3479,p3480,p3481,p3482,p3483,p3484,p3485,p3486,p3487,p3488,p3489,p3490,p3491,p3492,p3493,p3494,p3495,p3496,p3497,p3498,p3499,p3500]),
	%use_asp_equil1([p3501,p3502,p3503,p3504,p3505,p3506,p3507,p3508,p3509,p3510,p3511,p3512,p3513,p3514,p3515,p3516,p3517,p3518,p3519,p3520,p3521,p3522,p3523,p3524,p3525,p3526,p3527,p3528,p3529,p3530,p3531,p3532,p3533,p3534,p3535,p3536,p3537,p3538,p3539,p3540,p3541,p3542,p3543,p3544,p3545,p3546,p3547,p3548,p3549,p3550,p3551,p3552,p3553,p3554,p3555,p3556,p3557,p3558,p3559,p3560,p3561,p3562,p3563,p3564,p3565,p3566,p3567,p3568,p3569,p3570,p3571,p3572,p3573,p3574,p3575,p3576,p3577,p3578,p3579,p3580,p3581,p3582,p3583,p3584,p3585,p3586,p3587,p3588,p3589,p3590,p3591,p3592,p3593,p3594,p3595,p3596,p3597,p3598,p3599,p3600,p3601,p3602,p3603,p3604,p3605,p3606,p3607,p3608,p3609,p3610,p3611,p3612,p3613,p3614,p3615,p3616,p3617,p3618,p3619,p3620,p3621,p3622,p3623,p3624,p3625,p3626,p3627,p3628,p3629,p3630,p3631,p3632,p3633,p3634,p3635,p3636,p3637,p3638,p3639,p3640,p3641,p3642,p3643,p3644,p3645,p3646,p3647,p3648,p3649,p3650,p3651,p3652,p3653,p3654,p3655,p3656,p3657,p3658,p3659,p3660,p3661,p3662,p3663,p3664,p3665,p3666,p3667,p3668,p3669,p3670,p3671,p3672,p3673,p3674,p3675,p3676,p3677,p3678,p3679,p3680,p3681,p3682,p3683,p3684,p3685,p3686,p3687,p3688,p3689,p3690,p3691,p3692,p3693,p3694,p3695,p3696,p3697,p3698,p3699,p3700,p3701,p3702,p3703,p3704,p3705,p3706,p3707,p3708,p3709,p3710,p3711,p3712,p3713,p3714,p3715,p3716,p3717,p3718,p3719,p3720,p3721,p3722,p3723,p3724,p3725,p3726,p3727,p3728,p3729,p3730,p3731,p3732,p3733,p3734,p3735,p3736,p3737,p3738,p3739,p3740,p3741,p3742,p3743,p3744,p3745,p3746,p3747,p3748,p3749,p3750,p3751,p3752,p3753,p3754,p3755,p3756,p3757,p3758,p3759,p3760,p3761,p3762,p3763,p3764,p3765,p3766,p3767,p3768,p3769,p3770,p3771,p3772,p3773,p3774,p3775,p3776,p3777,p3778,p3779,p3780,p3781,p3782,p3783,p3784,p3785,p3786,p3787,p3788,p3789,p3790,p3791,p3792,p3793,p3794,p3795,p3796,p3797,p3798,p3799,p3800,p3801,p3802,p3803,p3804,p3805,p3806,p3807,p3808,p3809,p3810,p3811,p3812,p3813,p3814,p3815,p3816,p3817,p3818,p3819,p3820,p3821,p3822,p3823,p3824,p3825,p3826,p3827,p3828,p3829,p3830,p3831,p3832,p3833,p3834,p3835,p3836,p3837,p3838,p3839,p3840,p3841,p3842,p3843,p3844,p3845,p3846,p3847,p3848,p3849,p3850,p3851,p3852,p3853,p3854,p3855,p3856,p3857,p3858,p3859,p3860,p3861,p3862,p3863,p3864,p3865,p3866,p3867,p3868,p3869,p3870,p3871,p3872,p3873,p3874,p3875,p3876,p3877,p3878,p3879,p3880,p3881,p3882,p3883,p3884,p3885,p3886,p3887,p3888,p3889,p3890,p3891,p3892,p3893,p3894,p3895,p3896,p3897,p3898,p3899,p3900,p3901,p3902,p3903,p3904,p3905,p3906,p3907,p3908,p3909,p3910,p3911,p3912,p3913,p3914,p3915,p3916,p3917,p3918,p3919,p3920,p3921,p3922,p3923,p3924,p3925,p3926,p3927,p3928,p3929,p3930,p3931,p3932,p3933,p3934,p3935,p3936,p3937,p3938,p3939,p3940,p3941,p3942,p3943,p3944,p3945,p3946,p3947,p3948,p3949,p3950,p3951,p3952,p3953,p3954,p3955,p3956,p3957,p3958,p3959,p3960,p3961,p3962,p3963,p3964,p3965,p3966,p3967,p3968,p3969,p3970,p3971,p3972,p3973,p3974,p3975,p3976,p3977,p3978,p3979,p3980,p3981,p3982,p3983,p3984,p3985,p3986,p3987,p3988,p3989,p3990,p3991,p3992,p3993,p3994,p3995,p3996,p3997,p3998,p3999,p4000]),
	%use_asp_equil1([p4001,p4002,p4003,p4004,p4005,p4006,p4007,p4008,p4009,p4010,p4011,p4012,p4013,p4014,p4015,p4016,p4017,p4018,p4019,p4020,p4021,p4022,p4023,p4024,p4025,p4026,p4027,p4028,p4029,p4030,p4031,p4032,p4033,p4034,p4035,p4036,p4037,p4038,p4039,p4040,p4041,p4042,p4043,p4044,p4045,p4046,p4047,p4048,p4049,p4050,p4051,p4052,p4053,p4054,p4055,p4056,p4057,p4058,p4059,p4060,p4061,p4062,p4063,p4064,p4065,p4066,p4067,p4068,p4069,p4070,p4071,p4072,p4073,p4074,p4075,p4076,p4077,p4078,p4079,p4080,p4081,p4082,p4083,p4084,p4085,p4086,p4087,p4088,p4089,p4090,p4091,p4092,p4093,p4094,p4095,p4096,p4097,p4098,p4099,p4100,p4101,p4102,p4103,p4104,p4105,p4106,p4107,p4108,p4109,p4110,p4111,p4112,p4113,p4114,p4115,p4116,p4117,p4118,p4119,p4120,p4121,p4122,p4123,p4124,p4125,p4126,p4127,p4128,p4129,p4130,p4131,p4132,p4133,p4134,p4135,p4136,p4137,p4138,p4139,p4140,p4141,p4142,p4143,p4144,p4145,p4146,p4147,p4148,p4149,p4150,p4151,p4152,p4153,p4154,p4155,p4156,p4157,p4158,p4159,p4160,p4161,p4162,p4163,p4164,p4165,p4166,p4167,p4168,p4169,p4170,p4171,p4172,p4173,p4174,p4175,p4176,p4177,p4178,p4179,p4180,p4181,p4182,p4183,p4184,p4185,p4186,p4187,p4188,p4189,p4190,p4191,p4192,p4193,p4194,p4195,p4196,p4197,p4198,p4199,p4200,p4201,p4202,p4203,p4204,p4205,p4206,p4207,p4208,p4209,p4210,p4211,p4212,p4213,p4214,p4215,p4216,p4217,p4218,p4219,p4220,p4221,p4222,p4223,p4224,p4225,p4226,p4227,p4228,p4229,p4230,p4231,p4232,p4233,p4234,p4235,p4236,p4237,p4238,p4239,p4240,p4241,p4242,p4243,p4244,p4245,p4246,p4247,p4248,p4249,p4250,p4251,p4252,p4253,p4254,p4255,p4256,p4257,p4258,p4259,p4260,p4261,p4262,p4263,p4264,p4265,p4266,p4267,p4268,p4269,p4270,p4271,p4272,p4273,p4274,p4275,p4276,p4277,p4278,p4279,p4280,p4281,p4282,p4283,p4284,p4285,p4286,p4287,p4288,p4289,p4290,p4291,p4292,p4293,p4294,p4295,p4296,p4297,p4298,p4299,p4300,p4301,p4302,p4303,p4304,p4305,p4306,p4307,p4308,p4309,p4310,p4311,p4312,p4313,p4314,p4315,p4316,p4317,p4318,p4319,p4320,p4321,p4322,p4323,p4324,p4325,p4326,p4327,p4328,p4329,p4330,p4331,p4332,p4333,p4334,p4335,p4336,p4337,p4338,p4339,p4340,p4341,p4342,p4343,p4344,p4345,p4346,p4347,p4348,p4349,p4350,p4351,p4352,p4353,p4354,p4355,p4356,p4357,p4358,p4359,p4360,p4361,p4362,p4363,p4364,p4365,p4366,p4367,p4368,p4369,p4370,p4371,p4372,p4373,p4374,p4375,p4376,p4377,p4378,p4379,p4380,p4381,p4382,p4383,p4384,p4385,p4386,p4387,p4388,p4389,p4390,p4391,p4392,p4393,p4394,p4395,p4396,p4397,p4398,p4399,p4400,p4401,p4402,p4403,p4404,p4405,p4406,p4407,p4408,p4409,p4410,p4411,p4412,p4413,p4414,p4415,p4416,p4417,p4418,p4419,p4420,p4421,p4422,p4423,p4424,p4425,p4426,p4427,p4428,p4429,p4430,p4431,p4432,p4433,p4434,p4435,p4436,p4437,p4438,p4439,p4440,p4441,p4442,p4443,p4444,p4445,p4446,p4447,p4448,p4449,p4450,p4451,p4452,p4453,p4454,p4455,p4456,p4457,p4458,p4459,p4460,p4461,p4462,p4463,p4464,p4465,p4466,p4467,p4468,p4469,p4470,p4471,p4472,p4473,p4474,p4475,p4476,p4477,p4478,p4479,p4480,p4481,p4482,p4483,p4484,p4485,p4486,p4487,p4488,p4489,p4490,p4491,p4492,p4493,p4494,p4495,p4496,p4497,p4498,p4499,p4500,p4501,p4502,p4503,p4504,p4505,p4506,p4507,p4508,p4509,p4510,p4511,p4512,p4513,p4514,p4515,p4516,p4517,p4518,p4519,p4520,p4521,p4522,p4523,p4524,p4525,p4526,p4527,p4528,p4529,p4530,p4531,p4532,p4533,p4534,p4535,p4536,p4537,p4538,p4539,p4540,p4541,p4542,p4543,p4544,p4545,p4546,p4547,p4548,p4549,p4550,p4551,p4552,p4553,p4554,p4555,p4556,p4557,p4558,p4559,p4560,p4561,p4562,p4563,p4564,p4565,p4566,p4567,p4568,p4569,p4570,p4571,p4572,p4573,p4574,p4575,p4576,p4577,p4578,p4579,p4580,p4581,p4582,p4583,p4584,p4585,p4586,p4587,p4588,p4589,p4590,p4591,p4592,p4593,p4594,p4595,p4596,p4597,p4598,p4599,p4600]),
	%use_asp_equil1([p4601,p4602,p4603,p4604,p4605,p4606,p4607,p4608,p4609,p4610,p4611,p4612,p4613,p4614,p4615,p4616,p4617,p4618,p4619,p4620,p4621,p4622,p4623,p4624,p4625,p4626,p4627,p4628,p4629,p4630,p4631,p4632,p4633,p4634,p4635,p4636,p4637,p4638,p4639,p4640,p4641,p4642,p4643,p4644,p4645,p4646,p4647,p4648,p4649,p4650,p4651,p4652,p4653,p4654,p4655,p4656,p4657,p4658,p4659,p4660,p4661,p4662,p4663,p4664,p4665,p4666,p4667,p4668,p4669,p4670,p4671,p4672,p4673,p4674,p4675,p4676,p4677,p4678,p4679,p4680,p4681,p4682,p4683,p4684,p4685,p4686,p4687,p4688,p4689,p4690,p4691,p4692,p4693,p4694,p4695,p4696,p4697,p4698,p4699,p4700,p4701,p4702,p4703,p4704,p4705,p4706,p4707,p4708,p4709,p4710,p4711,p4712,p4713,p4714,p4715,p4716,p4717,p4718,p4719,p4720,p4721,p4722,p4723,p4724,p4725,p4726,p4727,p4728,p4729,p4730,p4731,p4732,p4733,p4734,p4735,p4736,p4737,p4738,p4739,p4740,p4741,p4742,p4743,p4744,p4745,p4746,p4747,p4748,p4749,p4750,p4751,p4752,p4753,p4754,p4755,p4756,p4757,p4758,p4759,p4760,p4761,p4762,p4763,p4764,p4765,p4766,p4767,p4768,p4769,p4770,p4771,p4772,p4773,p4774,p4775,p4776,p4777,p4778,p4779,p4780,p4781,p4782,p4783,p4784,p4785,p4786,p4787,p4788,p4789,p4790,p4791,p4792,p4793,p4794,p4795,p4796,p4797,p4798,p4799,p4800,p4801,p4802,p4803,p4804,p4805,p4806,p4807,p4808,p4809,p4810,p4811,p4812,p4813,p4814,p4815,p4816,p4817,p4818,p4819,p4820,p4821,p4822,p4823,p4824,p4825,p4826,p4827,p4828,p4829,p4830,p4831,p4832,p4833,p4834,p4835,p4836,p4837,p4838,p4839,p4840,p4841,p4842,p4843,p4844,p4845,p4846,p4847,p4848,p4849,p4850,p4851,p4852,p4853,p4854,p4855,p4856,p4857,p4858,p4859,p4860,p4861,p4862,p4863,p4864,p4865,p4866,p4867,p4868,p4869,p4870,p4871,p4872,p4873,p4874,p4875,p4876,p4877,p4878,p4879,p4880,p4881,p4882,p4883,p4884,p4885,p4886,p4887,p4888,p4889,p4890,p4891,p4892,p4893,p4894,p4895,p4896,p4897,p4898,p4899,p4900,p4901,p4902,p4903,p4904,p4905,p4906,p4907,p4908,p4909,p4910,p4911,p4912,p4913,p4914,p4915,p4916,p4917,p4918,p4919,p4920,p4921,p4922,p4923,p4924,p4925,p4926,p4927,p4928,p4929,p4930,p4931,p4932,p4933,p4934,p4935,p4936,p4937,p4938,p4939,p4940,p4941,p4942,p4943,p4944,p4945,p4946,p4947,p4948,p4949,p4950,p4951,p4952,p4953,p4954,p4955,p4956,p4957,p4958,p4959,p4960,p4961,p4962,p4963,p4964,p4965,p4966,p4967,p4968,p4969,p4970,p4971,p4972,p4973,p4974,p4975,p4976,p4977,p4978,p4979,p4980,p4981,p4982,p4983,p4984,p4985,p4986,p4987,p4988,p4989,p4990,p4991,p4992,p4993,p4994,p4995,p4996,p4997,p4998,p4999,p5000]),
	%use_asp_equil1([p5001,p5002,p5003,p5004,p5005,p5006,p5007,p5008,p5009,p5010,p5011,p5012,p5013,p5014,p5015,p5016,p5017,p5018,p5019,p5020,p5021,p5022,p5023,p5024,p5025,p5026,p5027,p5028,p5029,p5030,p5031,p5032,p5033,p5034,p5035,p5036,p5037,p5038,p5039,p5040,p5041,p5042,p5043,p5044,p5045,p5046,p5047,p5048,p5049,p5050,p5051,p5052,p5053,p5054,p5055,p5056,p5057,p5058,p5059,p5060,p5061,p5062,p5063,p5064,p5065,p5066,p5067,p5068,p5069,p5070,p5071,p5072,p5073,p5074,p5075,p5076,p5077,p5078,p5079,p5080,p5081,p5082,p5083,p5084,p5085,p5086,p5087,p5088,p5089,p5090,p5091,p5092,p5093,p5094,p5095,p5096,p5097,p5098,p5099,p5100,p5101,p5102,p5103,p5104,p5105,p5106,p5107,p5108,p5109,p5110,p5111,p5112,p5113,p5114,p5115,p5116,p5117,p5118,p5119,p5120,p5121,p5122,p5123,p5124,p5125,p5126,p5127,p5128,p5129,p5130,p5131,p5132,p5133,p5134,p5135,p5136,p5137,p5138,p5139,p5140,p5141,p5142,p5143,p5144,p5145,p5146,p5147,p5148,p5149,p5150,p5151,p5152,p5153,p5154,p5155,p5156,p5157,p5158,p5159,p5160,p5161,p5162,p5163,p5164,p5165,p5166,p5167,p5168,p5169,p5170,p5171,p5172,p5173,p5174,p5175,p5176,p5177,p5178,p5179,p5180,p5181,p5182,p5183,p5184,p5185,p5186,p5187,p5188,p5189,p5190,p5191,p5192,p5193,p5194,p5195,p5196,p5197,p5198,p5199,p5200,p5201,p5202,p5203,p5204,p5205,p5206,p5207,p5208,p5209,p5210,p5211,p5212,p5213,p5214,p5215,p5216,p5217,p5218,p5219,p5220,p5221,p5222,p5223,p5224,p5225,p5226,p5227,p5228,p5229,p5230,p5231,p5232,p5233,p5234,p5235,p5236,p5237,p5238,p5239,p5240,p5241,p5242,p5243,p5244,p5245,p5246,p5247,p5248,p5249,p5250,p5251,p5252,p5253,p5254,p5255,p5256,p5257,p5258,p5259,p5260,p5261,p5262,p5263,p5264,p5265,p5266,p5267,p5268,p5269,p5270,p5271,p5272,p5273,p5274,p5275,p5276,p5277,p5278,p5279,p5280,p5281,p5282,p5283,p5284,p5285,p5286,p5287,p5288,p5289,p5290,p5291,p5292,p5293,p5294,p5295,p5296,p5297,p5298,p5299,p5300,p5301,p5302,p5303,p5304,p5305,p5306,p5307,p5308,p5309,p5310,p5311,p5312,p5313,p5314,p5315,p5316,p5317,p5318,p5319,p5320,p5321,p5322,p5323,p5324,p5325,p5326,p5327,p5328,p5329,p5330,p5331,p5332,p5333,p5334,p5335,p5336,p5337,p5338,p5339,p5340,p5341,p5342,p5343,p5344,p5345,p5346,p5347,p5348,p5349,p5350,p5351,p5352,p5353,p5354,p5355,p5356,p5357,p5358,p5359,p5360,p5361,p5362,p5363,p5364,p5365,p5366,p5367,p5368,p5369,p5370,p5371,p5372,p5373,p5374,p5375,p5376,p5377,p5378,p5379,p5380,p5381,p5382,p5383,p5384,p5385,p5386,p5387,p5388,p5389,p5390,p5391,p5392,p5393,p5394,p5395,p5396,p5397,p5398,p5399,p5400,p5401,p5402,p5403,p5404,p5405,p5406,p5407,p5408,p5409,p5410,p5411,p5412,p5413,p5414,p5415,p5416,p5417,p5418,p5419,p5420,p5421,p5422,p5423,p5424,p5425,p5426,p5427,p5428,p5429,p5430,p5431,p5432,p5433,p5434,p5435,p5436,p5437,p5438,p5439,p5440,p5441,p5442,p5443,p5444,p5445,p5446,p5447,p5448,p5449,p5450,p5451,p5452,p5453,p5454,p5455,p5456,p5457,p5458,p5459,p5460,p5461,p5462,p5463,p5464,p5465,p5466,p5467,p5468,p5469,p5470,p5471,p5472,p5473,p5474,p5475,p5476,p5477,p5478,p5479,p5480,p5481,p5482,p5483,p5484,p5485,p5486,p5487,p5488,p5489,p5490,p5491,p5492,p5493,p5494,p5495,p5496,p5497,p5498,p5499,p5500]),
	%use_asp_equil1([p5501,p5502,p5503,p5504,p5505,p5506,p5507,p5508,p5509,p5510,p5511,p5512,p5513,p5514,p5515,p5516,p5517,p5518,p5519,p5520,p5521,p5522,p5523,p5524,p5525,p5526,p5527,p5528,p5529,p5530,p5531,p5532,p5533,p5534,p5535,p5536,p5537,p5538,p5539,p5540,p5541,p5542,p5543,p5544,p5545,p5546,p5547,p5548,p5549,p5550,p5551,p5552,p5553,p5554,p5555,p5556,p5557,p5558,p5559,p5560,p5561,p5562,p5563,p5564,p5565,p5566,p5567,p5568,p5569,p5570,p5571,p5572,p5573,p5574,p5575,p5576,p5577,p5578,p5579,p5580,p5581,p5582,p5583,p5584,p5585,p5586,p5587,p5588,p5589,p5590,p5591,p5592,p5593,p5594,p5595,p5596,p5597,p5598,p5599,p5600,p5601,p5602,p5603,p5604,p5605,p5606,p5607,p5608,p5609,p5610,p5611,p5612,p5613,p5614,p5615,p5616,p5617,p5618,p5619,p5620,p5621,p5622,p5623,p5624,p5625,p5626,p5627,p5628,p5629,p5630,p5631,p5632,p5633,p5634,p5635,p5636,p5637,p5638,p5639,p5640,p5641,p5642,p5643,p5644,p5645,p5646,p5647,p5648,p5649,p5650,p5651,p5652,p5653,p5654,p5655,p5656,p5657,p5658,p5659,p5660,p5661,p5662,p5663,p5664,p5665,p5666,p5667,p5668,p5669,p5670,p5671,p5672,p5673,p5674,p5675,p5676,p5677,p5678,p5679,p5680,p5681,p5682,p5683,p5684,p5685,p5686,p5687,p5688,p5689,p5690,p5691,p5692,p5693,p5694,p5695,p5696,p5697,p5698,p5699,p5700,p5701,p5702,p5703,p5704,p5705,p5706,p5707,p5708,p5709,p5710,p5711,p5712,p5713,p5714,p5715,p5716,p5717,p5718,p5719,p5720,p5721,p5722,p5723,p5724,p5725,p5726,p5727,p5728,p5729,p5730,p5731,p5732,p5733,p5734,p5735,p5736,p5737,p5738,p5739,p5740,p5741,p5742,p5743,p5744,p5745,p5746,p5747,p5748,p5749,p5750,p5751,p5752,p5753,p5754,p5755,p5756,p5757,p5758,p5759,p5760,p5761,p5762,p5763,p5764,p5765,p5766,p5767,p5768,p5769,p5770,p5771,p5772,p5773,p5774,p5775,p5776,p5777,p5778,p5779,p5780,p5781,p5782,p5783,p5784,p5785,p5786,p5787,p5788,p5789,p5790,p5791,p5792,p5793,p5794,p5795,p5796,p5797,p5798,p5799,p5800,p5801,p5802,p5803,p5804,p5805,p5806,p5807,p5808,p5809,p5810,p5811,p5812,p5813,p5814,p5815,p5816,p5817,p5818,p5819,p5820,p5821,p5822,p5823,p5824,p5825,p5826,p5827,p5828,p5829,p5830,p5831,p5832,p5833,p5834,p5835,p5836,p5837,p5838,p5839,p5840,p5841,p5842,p5843,p5844,p5845,p5846,p5847,p5848,p5849,p5850,p5851,p5852,p5853,p5854,p5855,p5856,p5857,p5858,p5859,p5860,p5861,p5862,p5863,p5864,p5865,p5866,p5867,p5868,p5869,p5870,p5871,p5872,p5873,p5874,p5875,p5876,p5877,p5878,p5879,p5880,p5881,p5882,p5883,p5884,p5885,p5886,p5887,p5888,p5889,p5890,p5891,p5892,p5893,p5894,p5895,p5896,p5897,p5898,p5899,p5900,p5901,p5902,p5903,p5904,p5905,p5906,p5907,p5908,p5909,p5910,p5911,p5912,p5913,p5914,p5915,p5916,p5917,p5918,p5919,p5920,p5921,p5922,p5923,p5924,p5925,p5926,p5927,p5928,p5929,p5930,p5931,p5932,p5933,p5934,p5935,p5936,p5937,p5938,p5939,p5940,p5941,p5942,p5943,p5944,p5945,p5946,p5947,p5948,p5949,p5950,p5951,p5952,p5953,p5954,p5955,p5956,p5957,p5958,p5959,p5960,p5961,p5962,p5963,p5964,p5965,p5966,p5967,p5968,p5969,p5970,p5971,p5972,p5973,p5974,p5975,p5976,p5977,p5978,p5979,p5980,p5981,p5982,p5983,p5984,p5985,p5986,p5987,p5988,p5989,p5990,p5991,p5992,p5993,p5994,p5995,p5996,p5997,p5998,p5999,p6000]),
	%use_asp_equil1([p6001,p6002,p6003,p6004,p6005,p6006,p6007,p6008,p6009,p6010,p6011,p6012,p6013,p6014,p6015,p6016,p6017,p6018,p6019,p6020,p6021,p6022,p6023,p6024,p6025,p6026,p6027,p6028,p6029,p6030,p6031,p6032,p6033,p6034,p6035,p6036,p6037,p6038,p6039,p6040,p6041,p6042,p6043,p6044,p6045,p6046,p6047,p6048,p6049,p6050,p6051,p6052,p6053,p6054,p6055,p6056,p6057,p6058,p6059,p6060,p6061,p6062,p6063,p6064,p6065,p6066,p6067,p6068,p6069,p6070,p6071,p6072,p6073,p6074,p6075,p6076,p6077,p6078,p6079,p6080,p6081,p6082,p6083,p6084,p6085,p6086,p6087,p6088,p6089,p6090,p6091,p6092,p6093,p6094,p6095,p6096,p6097,p6098,p6099,p6100,p6101,p6102,p6103,p6104,p6105,p6106,p6107,p6108,p6109,p6110,p6111,p6112,p6113,p6114,p6115,p6116,p6117,p6118,p6119,p6120,p6121,p6122,p6123,p6124,p6125,p6126,p6127,p6128,p6129,p6130,p6131,p6132,p6133,p6134,p6135,p6136,p6137,p6138,p6139,p6140,p6141,p6142,p6143,p6144,p6145,p6146,p6147,p6148,p6149,p6150,p6151,p6152,p6153,p6154,p6155,p6156,p6157,p6158,p6159,p6160,p6161,p6162,p6163,p6164,p6165,p6166,p6167,p6168,p6169,p6170,p6171,p6172,p6173,p6174,p6175,p6176,p6177,p6178,p6179,p6180,p6181,p6182,p6183,p6184,p6185,p6186,p6187,p6188,p6189,p6190,p6191,p6192,p6193,p6194,p6195,p6196,p6197,p6198,p6199,p6200,p6201,p6202,p6203,p6204,p6205,p6206,p6207,p6208,p6209,p6210,p6211,p6212,p6213,p6214,p6215,p6216,p6217,p6218,p6219,p6220,p6221,p6222,p6223,p6224,p6225,p6226,p6227,p6228,p6229,p6230,p6231,p6232,p6233,p6234,p6235,p6236,p6237,p6238,p6239,p6240,p6241,p6242,p6243,p6244,p6245,p6246,p6247,p6248,p6249,p6250,p6251,p6252,p6253,p6254,p6255,p6256,p6257,p6258,p6259,p6260,p6261,p6262,p6263,p6264,p6265,p6266,p6267,p6268,p6269,p6270,p6271,p6272,p6273,p6274,p6275,p6276,p6277,p6278,p6279,p6280,p6281,p6282,p6283,p6284,p6285,p6286,p6287,p6288,p6289,p6290,p6291,p6292,p6293,p6294,p6295,p6296,p6297,p6298,p6299,p6300,p6301,p6302,p6303,p6304,p6305,p6306,p6307,p6308,p6309,p6310,p6311,p6312,p6313,p6314,p6315,p6316,p6317,p6318,p6319,p6320,p6321,p6322,p6323,p6324,p6325,p6326,p6327,p6328,p6329,p6330,p6331,p6332,p6333,p6334,p6335,p6336,p6337,p6338,p6339,p6340,p6341,p6342,p6343,p6344,p6345,p6346,p6347,p6348,p6349,p6350,p6351,p6352,p6353,p6354,p6355,p6356,p6357,p6358,p6359,p6360,p6361,p6362,p6363,p6364,p6365,p6366,p6367,p6368,p6369,p6370,p6371,p6372,p6373,p6374,p6375,p6376,p6377,p6378,p6379,p6380,p6381,p6382,p6383,p6384,p6385,p6386,p6387,p6388,p6389,p6390,p6391,p6392,p6393,p6394,p6395,p6396,p6397,p6398,p6399,p6400,p6401,p6402,p6403,p6404,p6405,p6406,p6407,p6408,p6409,p6410,p6411,p6412,p6413,p6414,p6415,p6416,p6417,p6418,p6419,p6420,p6421,p6422,p6423,p6424,p6425,p6426,p6427,p6428,p6429,p6430,p6431,p6432,p6433,p6434,p6435,p6436,p6437,p6438,p6439,p6440,p6441,p6442,p6443,p6444,p6445,p6446,p6447,p6448,p6449,p6450,p6451,p6452,p6453,p6454,p6455,p6456,p6457,p6458,p6459,p6460,p6461,p6462,p6463,p6464,p6465,p6466,p6467,p6468,p6469,p6470,p6471,p6472,p6473,p6474,p6475,p6476,p6477,p6478,p6479,p6480,p6481,p6482,p6483,p6484,p6485,p6486,p6487,p6488,p6489,p6490,p6491,p6492,p6493,p6494,p6495,p6496,p6497,p6498,p6499,p6500]),
	%use_asp_equil1([p6501,p6502,p6503,p6504,p6505,p6506,p6507,p6508,p6509,p6510,p6511,p6512,p6513,p6514,p6515,p6516,p6517,p6518,p6519,p6520,p6521,p6522,p6523,p6524,p6525,p6526,p6527,p6528,p6529,p6530,p6531,p6532,p6533,p6534,p6535,p6536,p6537,p6538,p6539,p6540,p6541,p6542,p6543,p6544,p6545,p6546,p6547,p6548,p6549,p6550,p6551,p6552,p6553,p6554,p6555,p6556,p6557,p6558,p6559,p6560,p6561,p6562,p6563,p6564,p6565,p6566,p6567,p6568,p6569,p6570,p6571,p6572,p6573,p6574,p6575,p6576,p6577,p6578,p6579,p6580,p6581,p6582,p6583,p6584,p6585,p6586,p6587,p6588,p6589,p6590,p6591,p6592,p6593,p6594,p6595,p6596,p6597,p6598,p6599,p6600,p6601,p6602,p6603,p6604,p6605,p6606,p6607,p6608,p6609,p6610,p6611,p6612,p6613,p6614,p6615,p6616,p6617,p6618,p6619,p6620,p6621,p6622,p6623,p6624,p6625,p6626,p6627,p6628,p6629,p6630,p6631,p6632,p6633,p6634,p6635,p6636,p6637,p6638,p6639,p6640,p6641,p6642,p6643,p6644,p6645,p6646,p6647,p6648,p6649,p6650,p6651,p6652,p6653,p6654,p6655,p6656,p6657,p6658,p6659,p6660,p6661,p6662,p6663,p6664,p6665,p6666,p6667,p6668,p6669,p6670,p6671,p6672,p6673,p6674,p6675,p6676,p6677,p6678,p6679,p6680,p6681,p6682,p6683,p6684,p6685,p6686,p6687,p6688,p6689,p6690,p6691,p6692,p6693,p6694,p6695,p6696,p6697,p6698,p6699,p6700,p6701,p6702,p6703,p6704,p6705,p6706,p6707,p6708,p6709,p6710,p6711,p6712,p6713,p6714,p6715,p6716,p6717,p6718,p6719,p6720,p6721,p6722,p6723,p6724,p6725,p6726,p6727,p6728,p6729,p6730,p6731,p6732,p6733,p6734,p6735,p6736,p6737,p6738,p6739,p6740,p6741,p6742,p6743,p6744,p6745,p6746,p6747,p6748,p6749,p6750,p6751,p6752,p6753,p6754,p6755,p6756,p6757,p6758,p6759,p6760,p6761,p6762,p6763,p6764,p6765,p6766,p6767,p6768,p6769,p6770,p6771,p6772,p6773,p6774,p6775,p6776,p6777,p6778,p6779,p6780,p6781,p6782,p6783,p6784,p6785,p6786,p6787,p6788,p6789,p6790,p6791,p6792,p6793,p6794,p6795,p6796,p6797,p6798,p6799,p6800,p6801,p6802,p6803,p6804,p6805,p6806,p6807,p6808,p6809,p6810,p6811,p6812,p6813,p6814,p6815,p6816,p6817,p6818,p6819,p6820,p6821,p6822,p6823,p6824,p6825,p6826,p6827,p6828,p6829,p6830,p6831,p6832,p6833,p6834,p6835,p6836,p6837,p6838,p6839,p6840,p6841,p6842,p6843,p6844,p6845,p6846,p6847,p6848,p6849,p6850,p6851,p6852,p6853,p6854,p6855,p6856,p6857,p6858,p6859,p6860,p6861,p6862,p6863,p6864,p6865,p6866,p6867,p6868,p6869,p6870,p6871,p6872,p6873,p6874,p6875,p6876,p6877,p6878,p6879,p6880,p6881,p6882,p6883,p6884,p6885,p6886,p6887,p6888,p6889,p6890,p6891,p6892,p6893,p6894,p6895,p6896,p6897,p6898,p6899,p6900,p6901,p6902,p6903,p6904,p6905,p6906,p6907,p6908,p6909,p6910,p6911,p6912,p6913,p6914,p6915,p6916,p6917,p6918,p6919,p6920,p6921,p6922,p6923,p6924,p6925,p6926,p6927,p6928,p6929,p6930,p6931,p6932,p6933,p6934,p6935,p6936,p6937,p6938,p6939,p6940,p6941,p6942,p6943,p6944,p6945,p6946,p6947,p6948,p6949,p6950,p6951,p6952,p6953,p6954,p6955,p6956,p6957,p6958,p6959,p6960,p6961,p6962,p6963,p6964,p6965,p6966,p6967,p6968,p6969,p6970,p6971,p6972,p6973,p6974,p6975,p6976,p6977,p6978,p6979,p6980,p6981,p6982,p6983,p6984,p6985,p6986,p6987,p6988,p6989,p6990,p6991,p6992,p6993,p6994,p6995,p6996,p6997,p6998,p6999,p7000]),	
	%use_asp_equil1([p7001,p7002,p7003,p7004,p7005,p7006,p7007,p7008,p7009,p7010,p7011,p7012,p7013,p7014,p7015,p7016,p7017,p7018,p7019,p7020,p7021,p7022,p7023,p7024,p7025,p7026,p7027,p7028,p7029,p7030,p7031,p7032,p7033,p7034,p7035,p7036,p7037,p7038,p7039,p7040,p7041,p7042,p7043,p7044,p7045,p7046,p7047,p7048,p7049,p7050,p7051,p7052,p7053,p7054,p7055,p7056,p7057,p7058,p7059,p7060,p7061,p7062,p7063,p7064,p7065,p7066,p7067,p7068,p7069,p7070,p7071,p7072,p7073,p7074,p7075,p7076,p7077,p7078,p7079,p7080,p7081,p7082,p7083,p7084,p7085,p7086,p7087,p7088,p7089,p7090,p7091,p7092,p7093,p7094,p7095,p7096,p7097,p7098,p7099,p7100,p7101,p7102,p7103,p7104,p7105,p7106,p7107,p7108,p7109,p7110,p7111,p7112,p7113,p7114,p7115,p7116,p7117,p7118,p7119,p7120,p7121,p7122,p7123,p7124,p7125,p7126,p7127,p7128,p7129,p7130,p7131,p7132,p7133,p7134,p7135,p7136,p7137,p7138,p7139,p7140,p7141,p7142,p7143,p7144,p7145,p7146,p7147,p7148,p7149,p7150,p7151,p7152,p7153,p7154,p7155,p7156,p7157,p7158,p7159,p7160,p7161,p7162,p7163,p7164,p7165,p7166,p7167,p7168,p7169,p7170,p7171,p7172,p7173,p7174,p7175,p7176,p7177,p7178,p7179,p7180,p7181,p7182,p7183,p7184,p7185,p7186,p7187,p7188,p7189,p7190,p7191,p7192,p7193,p7194,p7195,p7196,p7197,p7198,p7199,p7200,p7201,p7202,p7203,p7204,p7205,p7206,p7207,p7208,p7209,p7210,p7211,p7212,p7213,p7214,p7215,p7216,p7217,p7218,p7219,p7220,p7221,p7222,p7223,p7224,p7225,p7226,p7227,p7228,p7229,p7230,p7231,p7232,p7233,p7234,p7235,p7236,p7237,p7238,p7239,p7240,p7241,p7242,p7243,p7244,p7245,p7246,p7247,p7248,p7249,p7250,p7251,p7252,p7253,p7254,p7255,p7256,p7257,p7258,p7259,p7260,p7261,p7262,p7263,p7264,p7265,p7266,p7267,p7268,p7269,p7270,p7271,p7272,p7273,p7274,p7275,p7276,p7277,p7278,p7279,p7280,p7281,p7282,p7283,p7284,p7285,p7286,p7287,p7288,p7289,p7290,p7291,p7292,p7293,p7294,p7295,p7296,p7297,p7298,p7299,p7300,p7301,p7302,p7303,p7304,p7305,p7306,p7307,p7308,p7309,p7310,p7311,p7312,p7313,p7314,p7315,p7316,p7317,p7318,p7319,p7320,p7321,p7322,p7323,p7324,p7325,p7326,p7327,p7328,p7329,p7330,p7331,p7332,p7333,p7334,p7335,p7336,p7337,p7338,p7339,p7340,p7341,p7342,p7343,p7344,p7345,p7346,p7347,p7348,p7349,p7350,p7351,p7352,p7353,p7354,p7355,p7356,p7357,p7358,p7359,p7360,p7361,p7362,p7363,p7364,p7365,p7366,p7367,p7368,p7369,p7370,p7371,p7372,p7373,p7374,p7375,p7376,p7377,p7378,p7379,p7380,p7381,p7382,p7383,p7384,p7385,p7386,p7387,p7388,p7389,p7390,p7391,p7392,p7393,p7394,p7395,p7396,p7397,p7398,p7399,p7400,p7401,p7402,p7403,p7404,p7405,p7406,p7407,p7408,p7409,p7410,p7411,p7412,p7413,p7414,p7415,p7416,p7417,p7418,p7419,p7420,p7421,p7422,p7423,p7424,p7425,p7426,p7427,p7428,p7429,p7430,p7431,p7432,p7433,p7434,p7435,p7436,p7437,p7438,p7439,p7440,p7441,p7442,p7443,p7444,p7445,p7446,p7447,p7448,p7449,p7450,p7451,p7452,p7453,p7454,p7455,p7456,p7457,p7458,p7459,p7460,p7461,p7462,p7463,p7464,p7465,p7466,p7467,p7468,p7469,p7470,p7471,p7472,p7473,p7474,p7475,p7476,p7477,p7478,p7479,p7480,p7481,p7482,p7483,p7484,p7485,p7486,p7487,p7488,p7489,p7490,p7491,p7492,p7493,p7494,p7495,p7496,p7497,p7498,p7499,p7500]),	
	%use_asp_equil1([p7501,p7502,p7503,p7504,p7505,p7506,p7507,p7508,p7509,p7510,p7511,p7512,p7513,p7514,p7515,p7516,p7517,p7518,p7519,p7520,p7521,p7522,p7523,p7524,p7525,p7526,p7527,p7528,p7529,p7530,p7531,p7532,p7533,p7534,p7535,p7536,p7537,p7538,p7539,p7540,p7541,p7542,p7543,p7544,p7545,p7546,p7547,p7548,p7549,p7550,p7551,p7552,p7553,p7554,p7555,p7556,p7557,p7558,p7559,p7560,p7561,p7562,p7563,p7564,p7565,p7566,p7567,p7568,p7569,p7570,p7571,p7572,p7573,p7574,p7575,p7576,p7577,p7578,p7579,p7580,p7581,p7582,p7583,p7584,p7585,p7586,p7587,p7588,p7589,p7590,p7591,p7592,p7593,p7594,p7595,p7596,p7597,p7598,p7599,p7600,p7601,p7602,p7603,p7604,p7605,p7606,p7607,p7608,p7609,p7610,p7611,p7612,p7613,p7614,p7615,p7616,p7617,p7618,p7619,p7620,p7621,p7622,p7623,p7624,p7625,p7626,p7627,p7628,p7629,p7630,p7631,p7632,p7633,p7634,p7635,p7636,p7637,p7638,p7639,p7640,p7641,p7642,p7643,p7644,p7645,p7646,p7647,p7648,p7649,p7650,p7651,p7652,p7653,p7654,p7655,p7656,p7657,p7658,p7659,p7660,p7661,p7662,p7663,p7664,p7665,p7666,p7667,p7668,p7669,p7670,p7671,p7672,p7673,p7674,p7675,p7676,p7677,p7678,p7679,p7680,p7681,p7682,p7683,p7684,p7685,p7686,p7687,p7688,p7689,p7690,p7691,p7692,p7693,p7694,p7695,p7696,p7697,p7698,p7699,p7700,p7701,p7702,p7703,p7704,p7705,p7706,p7707,p7708,p7709,p7710,p7711,p7712,p7713,p7714,p7715,p7716,p7717,p7718,p7719,p7720,p7721,p7722,p7723,p7724,p7725,p7726,p7727,p7728,p7729,p7730,p7731,p7732,p7733,p7734,p7735,p7736,p7737,p7738,p7739,p7740,p7741,p7742,p7743,p7744,p7745,p7746,p7747,p7748,p7749,p7750,p7751,p7752,p7753,p7754,p7755,p7756,p7757,p7758,p7759,p7760,p7761,p7762,p7763,p7764,p7765,p7766,p7767,p7768,p7769,p7770,p7771,p7772,p7773,p7774,p7775,p7776,p7777,p7778,p7779,p7780,p7781,p7782,p7783,p7784,p7785,p7786,p7787,p7788,p7789,p7790,p7791,p7792,p7793,p7794,p7795,p7796,p7797,p7798,p7799,p7800,p7801,p7802,p7803,p7804,p7805,p7806,p7807,p7808,p7809,p7810,p7811,p7812,p7813,p7814,p7815,p7816,p7817,p7818,p7819,p7820,p7821,p7822,p7823,p7824,p7825,p7826,p7827,p7828,p7829,p7830,p7831,p7832,p7833,p7834,p7835,p7836,p7837,p7838,p7839,p7840,p7841,p7842,p7843,p7844,p7845,p7846,p7847,p7848,p7849,p7850,p7851,p7852,p7853,p7854,p7855,p7856,p7857,p7858,p7859,p7860,p7861,p7862,p7863,p7864,p7865,p7866,p7867,p7868,p7869,p7870,p7871,p7872,p7873,p7874,p7875,p7876,p7877,p7878,p7879,p7880,p7881,p7882,p7883,p7884,p7885,p7886,p7887,p7888,p7889,p7890,p7891,p7892,p7893,p7894,p7895,p7896,p7897,p7898,p7899,p7900,p7901,p7902,p7903,p7904,p7905,p7906,p7907,p7908,p7909,p7910,p7911,p7912,p7913,p7914,p7915,p7916,p7917,p7918,p7919,p7920,p7921,p7922,p7923,p7924,p7925,p7926,p7927,p7928,p7929,p7930,p7931,p7932,p7933,p7934,p7935,p7936,p7937,p7938,p7939,p7940,p7941,p7942,p7943,p7944,p7945,p7946,p7947,p7948,p7949,p7950,p7951,p7952,p7953,p7954,p7955,p7956,p7957,p7958,p7959,p7960,p7961,p7962,p7963,p7964,p7965,p7966,p7967,p7968,p7969,p7970,p7971,p7972,p7973,p7974,p7975,p7976,p7977,p7978,p7979,p7980,p7981,p7982,p7983,p7984,p7985,p7986,p7987,p7988,p7989,p7990,p7991,p7992,p7993,p7994,p7995,p7996,p7997,p7998,p7999,p8000]),	
	%use_asp_equil1([p8001,p8002,p8003,p8004,p8005,p8006,p8007,p8008,p8009,p8010,p8011,p8012,p8013,p8014,p8015,p8016,p8017,p8018,p8019,p8020,p8021,p8022,p8023,p8024,p8025,p8026,p8027,p8028,p8029,p8030,p8031,p8032,p8033,p8034,p8035,p8036,p8037,p8038,p8039,p8040,p8041,p8042,p8043,p8044,p8045,p8046,p8047,p8048,p8049,p8050,p8051,p8052,p8053,p8054,p8055,p8056,p8057,p8058,p8059,p8060,p8061,p8062,p8063,p8064,p8065,p8066,p8067,p8068,p8069,p8070,p8071,p8072,p8073,p8074,p8075,p8076,p8077,p8078,p8079,p8080,p8081,p8082,p8083,p8084,p8085,p8086,p8087,p8088,p8089,p8090,p8091,p8092,p8093,p8094,p8095,p8096,p8097,p8098,p8099,p8100,p8101,p8102,p8103,p8104,p8105,p8106,p8107,p8108,p8109,p8110,p8111,p8112,p8113,p8114,p8115,p8116,p8117,p8118,p8119,p8120,p8121,p8122,p8123,p8124,p8125,p8126,p8127,p8128,p8129,p8130,p8131,p8132,p8133,p8134,p8135,p8136,p8137,p8138,p8139,p8140,p8141,p8142,p8143,p8144,p8145,p8146,p8147,p8148,p8149,p8150,p8151,p8152,p8153,p8154,p8155,p8156,p8157,p8158,p8159,p8160,p8161,p8162,p8163,p8164,p8165,p8166,p8167,p8168,p8169,p8170,p8171,p8172,p8173,p8174,p8175,p8176,p8177,p8178,p8179,p8180,p8181,p8182,p8183,p8184,p8185,p8186,p8187,p8188,p8189,p8190,p8191,p8192,p8193,p8194,p8195,p8196,p8197,p8198,p8199,p8200,p8201,p8202,p8203,p8204,p8205,p8206,p8207,p8208,p8209,p8210,p8211,p8212,p8213,p8214,p8215,p8216,p8217,p8218,p8219,p8220,p8221,p8222,p8223,p8224,p8225,p8226,p8227,p8228,p8229,p8230,p8231,p8232,p8233,p8234,p8235,p8236,p8237,p8238,p8239,p8240,p8241,p8242,p8243,p8244,p8245,p8246,p8247,p8248,p8249,p8250,p8251,p8252,p8253,p8254,p8255,p8256,p8257,p8258,p8259,p8260,p8261,p8262,p8263,p8264,p8265,p8266,p8267,p8268,p8269,p8270,p8271,p8272,p8273,p8274,p8275,p8276,p8277,p8278,p8279,p8280,p8281,p8282,p8283,p8284,p8285,p8286,p8287,p8288,p8289,p8290,p8291,p8292,p8293,p8294,p8295,p8296,p8297,p8298,p8299,p8300,p8301,p8302,p8303,p8304,p8305,p8306,p8307,p8308,p8309,p8310,p8311,p8312,p8313,p8314,p8315,p8316,p8317,p8318,p8319,p8320,p8321,p8322,p8323,p8324,p8325,p8326,p8327,p8328,p8329,p8330,p8331,p8332,p8333,p8334,p8335,p8336,p8337,p8338,p8339,p8340,p8341,p8342,p8343,p8344,p8345,p8346,p8347,p8348,p8349,p8350,p8351,p8352,p8353,p8354,p8355,p8356,p8357,p8358,p8359,p8360,p8361,p8362,p8363,p8364,p8365,p8366,p8367,p8368,p8369,p8370,p8371,p8372,p8373,p8374,p8375,p8376,p8377,p8378,p8379,p8380,p8381,p8382,p8383,p8384,p8385,p8386,p8387,p8388,p8389,p8390,p8391,p8392,p8393,p8394,p8395,p8396,p8397,p8398,p8399,p8400,p8401,p8402,p8403,p8404,p8405,p8406,p8407,p8408,p8409,p8410,p8411,p8412,p8413,p8414,p8415,p8416,p8417,p8418,p8419,p8420,p8421,p8422,p8423,p8424,p8425,p8426,p8427,p8428,p8429,p8430,p8431,p8432,p8433,p8434,p8435,p8436,p8437,p8438,p8439,p8440,p8441,p8442,p8443,p8444,p8445,p8446,p8447,p8448,p8449,p8450,p8451,p8452,p8453,p8454,p8455,p8456,p8457,p8458,p8459,p8460,p8461,p8462,p8463,p8464,p8465,p8466,p8467,p8468,p8469,p8470,p8471,p8472,p8473,p8474,p8475,p8476,p8477,p8478,p8479,p8480,p8481,p8482,p8483,p8484,p8485,p8486,p8487,p8488,p8489,p8490,p8491,p8492,p8493,p8494,p8495,p8496,p8497,p8498,p8499,p8500]),	
	%use_asp_equil1([p8501,p8502,p8503,p8504,p8505,p8506,p8507,p8508,p8509,p8510,p8511,p8512,p8513,p8514,p8515,p8516,p8517,p8518,p8519,p8520,p8521,p8522,p8523,p8524,p8525,p8526,p8527,p8528,p8529,p8530,p8531,p8532,p8533,p8534,p8535,p8536,p8537,p8538,p8539,p8540,p8541,p8542,p8543,p8544,p8545,p8546,p8547,p8548,p8549,p8550,p8551,p8552,p8553,p8554,p8555,p8556,p8557,p8558,p8559,p8560,p8561,p8562,p8563,p8564,p8565,p8566,p8567,p8568,p8569,p8570,p8571,p8572,p8573,p8574,p8575,p8576,p8577,p8578,p8579,p8580,p8581,p8582,p8583,p8584,p8585,p8586,p8587,p8588,p8589,p8590,p8591,p8592,p8593,p8594,p8595,p8596,p8597,p8598,p8599,p8600,p8601,p8602,p8603,p8604,p8605,p8606,p8607,p8608,p8609,p8610,p8611,p8612,p8613,p8614,p8615,p8616,p8617,p8618,p8619,p8620,p8621,p8622,p8623,p8624,p8625,p8626,p8627,p8628,p8629,p8630,p8631,p8632,p8633,p8634,p8635,p8636,p8637,p8638,p8639,p8640,p8641,p8642,p8643,p8644,p8645,p8646,p8647,p8648,p8649,p8650,p8651,p8652,p8653,p8654,p8655,p8656,p8657,p8658,p8659,p8660,p8661,p8662,p8663,p8664,p8665,p8666,p8667,p8668,p8669,p8670,p8671,p8672,p8673,p8674,p8675,p8676,p8677,p8678,p8679,p8680,p8681,p8682,p8683,p8684,p8685,p8686,p8687,p8688,p8689,p8690,p8691,p8692,p8693,p8694,p8695,p8696,p8697,p8698,p8699,p8700,p8701,p8702,p8703,p8704,p8705,p8706,p8707,p8708,p8709,p8710,p8711,p8712,p8713,p8714,p8715,p8716,p8717,p8718,p8719,p8720,p8721,p8722,p8723,p8724,p8725,p8726,p8727,p8728,p8729,p8730,p8731,p8732,p8733,p8734,p8735,p8736,p8737,p8738,p8739,p8740,p8741,p8742,p8743,p8744,p8745,p8746,p8747,p8748,p8749,p8750,p8751,p8752,p8753,p8754,p8755,p8756,p8757,p8758,p8759,p8760,p8761,p8762,p8763,p8764,p8765,p8766,p8767,p8768,p8769,p8770,p8771,p8772,p8773,p8774,p8775,p8776,p8777,p8778,p8779,p8780,p8781,p8782,p8783,p8784,p8785,p8786,p8787,p8788,p8789,p8790,p8791,p8792,p8793,p8794,p8795,p8796,p8797,p8798,p8799,p8800,p8801,p8802,p8803,p8804,p8805,p8806,p8807,p8808,p8809,p8810,p8811,p8812,p8813,p8814,p8815,p8816,p8817,p8818,p8819,p8820,p8821,p8822,p8823,p8824,p8825,p8826,p8827,p8828,p8829,p8830,p8831,p8832,p8833,p8834,p8835,p8836,p8837,p8838,p8839,p8840,p8841,p8842,p8843,p8844,p8845,p8846,p8847,p8848,p8849,p8850,p8851,p8852,p8853,p8854,p8855,p8856,p8857,p8858,p8859,p8860,p8861,p8862,p8863,p8864,p8865,p8866,p8867,p8868,p8869,p8870,p8871,p8872,p8873,p8874,p8875,p8876,p8877,p8878,p8879,p8880,p8881,p8882,p8883,p8884,p8885,p8886,p8887,p8888,p8889,p8890,p8891,p8892,p8893,p8894,p8895,p8896,p8897,p8898,p8899,p8900,p8901,p8902,p8903,p8904,p8905,p8906,p8907,p8908,p8909,p8910,p8911,p8912,p8913,p8914,p8915,p8916,p8917,p8918,p8919,p8920,p8921,p8922,p8923,p8924,p8925,p8926,p8927,p8928,p8929,p8930,p8931,p8932,p8933,p8934,p8935,p8936,p8937,p8938,p8939,p8940,p8941,p8942,p8943,p8944,p8945,p8946,p8947,p8948,p8949,p8950,p8951,p8952,p8953,p8954,p8955,p8956,p8957,p8958,p8959,p8960,p8961,p8962,p8963,p8964,p8965,p8966,p8967,p8968,p8969,p8970,p8971,p8972,p8973,p8974,p8975,p8976,p8977,p8978,p8979,p8980,p8981,p8982,p8983,p8984,p8985,p8986,p8987,p8988,p8989,p8990,p8991,p8992,p8993,p8994,p8995,p8996,p8997,p8998,p8999,p9000]),	
	%use_asp_equil1([p9001,p9002,p9003,p9004,p9005,p9006,p9007,p9008,p9009,p9010,p9011,p9012,p9013,p9014,p9015,p9016,p9017,p9018,p9019,p9020,p9021,p9022,p9023,p9024,p9025,p9026,p9027,p9028,p9029,p9030,p9031,p9032,p9033,p9034,p9035,p9036,p9037,p9038,p9039,p9040,p9041,p9042,p9043,p9044,p9045,p9046,p9047,p9048,p9049,p9050,p9051,p9052,p9053,p9054,p9055,p9056,p9057,p9058,p9059,p9060,p9061,p9062,p9063,p9064,p9065,p9066,p9067,p9068,p9069,p9070,p9071,p9072,p9073,p9074,p9075,p9076,p9077,p9078,p9079,p9080,p9081,p9082,p9083,p9084,p9085,p9086,p9087,p9088,p9089,p9090,p9091,p9092,p9093,p9094,p9095,p9096,p9097,p9098,p9099,p9100,p9101,p9102,p9103,p9104,p9105,p9106,p9107,p9108,p9109,p9110,p9111,p9112,p9113,p9114,p9115,p9116,p9117,p9118,p9119,p9120,p9121,p9122,p9123,p9124,p9125,p9126,p9127,p9128,p9129,p9130,p9131,p9132,p9133,p9134,p9135,p9136,p9137,p9138,p9139,p9140,p9141,p9142,p9143,p9144,p9145,p9146,p9147,p9148,p9149,p9150,p9151,p9152,p9153,p9154,p9155,p9156,p9157,p9158,p9159,p9160,p9161,p9162,p9163,p9164,p9165,p9166,p9167,p9168,p9169,p9170,p9171,p9172,p9173,p9174,p9175,p9176,p9177,p9178,p9179,p9180,p9181,p9182,p9183,p9184,p9185,p9186,p9187,p9188,p9189,p9190,p9191,p9192,p9193,p9194,p9195,p9196,p9197,p9198,p9199,p9200,p9201,p9202,p9203,p9204,p9205,p9206,p9207,p9208,p9209,p9210,p9211,p9212,p9213,p9214,p9215,p9216,p9217,p9218,p9219,p9220,p9221,p9222,p9223,p9224,p9225,p9226,p9227,p9228,p9229,p9230,p9231,p9232,p9233,p9234,p9235,p9236,p9237,p9238,p9239,p9240,p9241,p9242,p9243,p9244,p9245,p9246,p9247,p9248,p9249,p9250,p9251,p9252,p9253,p9254,p9255,p9256,p9257,p9258,p9259,p9260,p9261,p9262,p9263,p9264,p9265,p9266,p9267,p9268,p9269,p9270,p9271,p9272,p9273,p9274,p9275,p9276,p9277,p9278,p9279,p9280,p9281,p9282,p9283,p9284,p9285,p9286,p9287,p9288,p9289,p9290,p9291,p9292,p9293,p9294,p9295,p9296,p9297,p9298,p9299,p9300,p9301,p9302,p9303,p9304,p9305,p9306,p9307,p9308,p9309,p9310,p9311,p9312,p9313,p9314,p9315,p9316,p9317,p9318,p9319,p9320,p9321,p9322,p9323,p9324,p9325,p9326,p9327,p9328,p9329,p9330,p9331,p9332,p9333,p9334,p9335,p9336,p9337,p9338,p9339,p9340,p9341,p9342,p9343,p9344,p9345,p9346,p9347,p9348,p9349,p9350,p9351,p9352,p9353,p9354,p9355,p9356,p9357,p9358,p9359,p9360,p9361,p9362,p9363,p9364,p9365,p9366,p9367,p9368,p9369,p9370,p9371,p9372,p9373,p9374,p9375,p9376,p9377,p9378,p9379,p9380,p9381,p9382,p9383,p9384,p9385,p9386,p9387,p9388,p9389,p9390,p9391,p9392,p9393,p9394,p9395,p9396,p9397,p9398,p9399,p9400,p9401,p9402,p9403,p9404,p9405,p9406,p9407,p9408,p9409,p9410,p9411,p9412,p9413,p9414,p9415,p9416,p9417,p9418,p9419,p9420,p9421,p9422,p9423,p9424,p9425,p9426,p9427,p9428,p9429,p9430,p9431,p9432,p9433,p9434,p9435,p9436,p9437,p9438,p9439,p9440,p9441,p9442,p9443,p9444,p9445,p9446,p9447,p9448,p9449,p9450,p9451,p9452,p9453,p9454,p9455,p9456,p9457,p9458,p9459,p9460,p9461,p9462,p9463,p9464,p9465,p9466,p9467,p9468,p9469,p9470,p9471,p9472,p9473,p9474,p9475,p9476,p9477,p9478,p9479,p9480,p9481,p9482,p9483,p9484,p9485,p9486,p9487,p9488,p9489,p9490,p9491,p9492,p9493,p9494,p9495,p9496,p9497,p9498,p9499,p9500]),
	%use_asp_equil1([p9501,p9502,p9503,p9504,p9505,p9506,p9507,p9508,p9509,p9510,p9511,p9512,p9513,p9514,p9515,p9516,p9517,p9518,p9519,p9520,p9521,p9522,p9523,p9524,p9525,p9526,p9527,p9528,p9529,p9530,p9531,p9532,p9533,p9534,p9535,p9536,p9537,p9538,p9539,p9540,p9541,p9542,p9543,p9544,p9545,p9546,p9547,p9548,p9549,p9550,p9551,p9552,p9553,p9554,p9555,p9556,p9557,p9558,p9559,p9560,p9561,p9562,p9563,p9564,p9565,p9566,p9567,p9568,p9569,p9570,p9571,p9572,p9573,p9574,p9575,p9576,p9577,p9578,p9579,p9580,p9581,p9582,p9583,p9584,p9585,p9586,p9587,p9588,p9589,p9590,p9591,p9592,p9593,p9594,p9595,p9596,p9597,p9598,p9599,p9600,p9601,p9602,p9603,p9604,p9605,p9606,p9607,p9608,p9609,p9610,p9611,p9612,p9613,p9614,p9615,p9616,p9617,p9618,p9619,p9620,p9621,p9622,p9623,p9624,p9625,p9626,p9627,p9628,p9629,p9630,p9631,p9632,p9633,p9634,p9635,p9636,p9637,p9638,p9639,p9640,p9641,p9642,p9643,p9644,p9645,p9646,p9647,p9648,p9649,p9650,p9651,p9652,p9653,p9654,p9655,p9656,p9657,p9658,p9659,p9660,p9661,p9662,p9663,p9664,p9665,p9666,p9667,p9668,p9669,p9670,p9671,p9672,p9673,p9674,p9675,p9676,p9677,p9678,p9679,p9680,p9681,p9682,p9683,p9684,p9685,p9686,p9687,p9688,p9689,p9690,p9691,p9692,p9693,p9694,p9695,p9696,p9697,p9698,p9699,p9700,p9701,p9702,p9703,p9704,p9705,p9706,p9707,p9708,p9709,p9710,p9711,p9712,p9713,p9714,p9715,p9716,p9717,p9718,p9719,p9720,p9721,p9722,p9723,p9724,p9725,p9726,p9727,p9728,p9729,p9730,p9731,p9732,p9733,p9734,p9735,p9736,p9737,p9738,p9739,p9740,p9741,p9742,p9743,p9744,p9745,p9746,p9747,p9748,p9749,p9750,p9751,p9752,p9753,p9754,p9755,p9756,p9757,p9758,p9759,p9760,p9761,p9762,p9763,p9764,p9765,p9766,p9767,p9768,p9769,p9770,p9771,p9772,p9773,p9774,p9775,p9776,p9777,p9778,p9779,p9780,p9781,p9782,p9783,p9784,p9785,p9786,p9787,p9788,p9789,p9790,p9791,p9792,p9793,p9794,p9795,p9796,p9797,p9798,p9799,p9800,p9801,p9802,p9803,p9804,p9805,p9806,p9807,p9808,p9809,p9810,p9811,p9812,p9813,p9814,p9815,p9816,p9817,p9818,p9819,p9820,p9821,p9822,p9823,p9824,p9825,p9826,p9827,p9828,p9829,p9830,p9831,p9832,p9833,p9834,p9835,p9836,p9837,p9838,p9839,p9840,p9841,p9842,p9843,p9844,p9845,p9846,p9847,p9848,p9849,p9850,p9851,p9852,p9853,p9854,p9855,p9856,p9857,p9858,p9859,p9860,p9861,p9862,p9863,p9864,p9865,p9866,p9867,p9868,p9869,p9870,p9871,p9872,p9873,p9874,p9875,p9876,p9877,p9878,p9879,p9880,p9881,p9882,p9883,p9884,p9885,p9886,p9887,p9888,p9889,p9890,p9891,p9892,p9893,p9894,p9895,p9896,p9897,p9898,p9899,p9900,p9901,p9902,p9903,p9904,p9905,p9906,p9907,p9908,p9909,p9910,p9911,p9912,p9913,p9914,p9915,p9916,p9917,p9918,p9919,p9920,p9921,p9922,p9923,p9924,p9925,p9926,p9927,p9928,p9929,p9930,p9931,p9932,p9933,p9934,p9935,p9936,p9937,p9938,p9939,p9940,p9941,p9942,p9943,p9944,p9945,p9946,p9947,p9948,p9949,p9950,p9951,p9952,p9953,p9954,p9955,p9956,p9957,p9958,p9959,p9960,p9961,p9962,p9963,p9964,p9965,p9966,p9967,p9968,p9969,p9970,p9971,p9972,p9973,p9974,p9975,p9976,p9977,p9978,p9979,p9980,p9981,p9982,p9983,p9984,p9985,p9986,p9987,p9988,p9989,p9990,p9991,p9992,p9993,p9994,p9995,p9996,p9997,p9998,p9999]),
	assert(buildSCC(1)), %%prepare for building SCC for whole graph
	retrieve_arc,
	start,
	retract(buildSCC(1)),
	assert(buildSCC(2)),
	statistics(walltime,[T_elapsed2,_]),
	T is T_elapsed2 - T_elapsed1,
	print_statistics(T).  %% prepare for break a SCC
	
	
	

use_asp_equil1(X):-
	%statistics(walltime,[T_elapsed1,_]),
	use_asp_equil(X).
	%statistics(walltime,[T_elapsed2,_]),
	%T is T_elapsed2 - T_elapsed1,
	%print_statistics(T).

use_asp_equil([Name|Tail]):-	
	assert(node(Name)),
	retractall(counting(_)),
	assert(counting(0)),
	assert(scc_node(Name)), %--for building strongly connected component
	retractall(dependency_number(_)),	
	assert(dependency_number(0)), %--for building dependency.		
	atom_concat(Name,'.lp',Filename), 
	atom_concat(Name,'tmp',TmpFile), 
	atom_concat(Name,'_asp',ASPFile),
	atom_concat(ASPFile,'.lp',ASPFileInput),
	file_exists(Filename),
	(on_exception(Err, compiledTMP(Name), (Err = existence_error(_,_))) 
 	-> 
	cleanup_module(Name),
	retractall(compiledTMP(Name)),
	(file_exists(TmpFile) -> CompiledFile=TmpFile; CompiledFile=Filename)
	;
	CompiledFile=Filename,
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['rm -f ', TmpFile]], [process(P1)]),
	process_wait(P1,exit(0))),
	create_asp(Name,ASPFile),
	%absolute_file_name('$SHELL', Shell1),
	process_create(Shell, ['-c', ['gringo ', ' ',' ', ASPFileInput, ' | clasp | grep UNSATIS | sed "s/^/\'/" |  sed -e \'s/$/ /\' -e "s/ /\'./" | sed \'s/UNSATISFIABLE/fail/\' ']], [stdout(pipe(Stream1))]),!,
	(test_unsatisfy(Stream1,Name) -> print('fail'),fail,close(Stream1) ;
	%print('true'),
	close(Stream1),
	atom_concat('model_',Name,Name1),
	%absolute_file_name('$SHELL', Shell), 
	process_create(Shell, ['-c', ['gringo ', ' ',' ', ASPFileInput, ' | clasp -n 0 |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\' -e \'/Optimization/d\' -e \'/OPTIMUM/,$d\' | sed -e "s/ \\(.\\)/\',\'\\1/g" -e \'s/$/ /\' -e "s/ /\'/" | sed -e = | sed -e \'N;s/\\n/ /\' -e "s/ /,\'/" -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name1,'_\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),!,
	read_from_stream(Stream,Name),
	assert(Name:(skept(P):-	findall(X,Name:model(X),List),
				asp:check_skept(P,List)
				)),			
	close(Stream),	
	write('hehelo'),write(compiledTMP(Name)),nl,
	assert(compiledTMP(Name))),	
	use_asp_equil(Tail).

use_asp_equil([]).

test_unsatisfy(Stream,_):-
	at_end_of_stream(Stream),!.	
	
test_unsatisfy(Stream,_):-
	\+ at_end_of_stream(Stream),
	%counting(X),	
	%X1 is X + 1,	
	%X < 500,
	%retractall(counting(_)),
	%assert(counting(X1)),
	%print(X),nl,
	read_line(Stream,Line),
	(Line  \== end_of_file ->
	((Line == [49,32] -> true
	;
	read_from_codes(Line,Modul)),!,	
	(Modul='fail' -> true; false));false).
	%assert(Name:model(ModulName)),
	%asp:create_modul(ModulName,ModulContent),
	%test_unsatisfy(Stream,Name));%test_unsatisfy(Stream,Name)).

%read_from_stream(Stream,_):-
%	print('read from stream begin71.\n'),
%	at_end_of_stream(Stream),
%	print('read from stream begin7.\n').	
	

%read_from_stream(Stream,Name):-
%	\+ at_end_of_stream,
%	%counting(X),	
%	%X1 is X + 1,	
%	%X < 500,
%	%retractall(counting(_)),
%	%assert(counting(X1)),
%	%print(X),nl,
%	read_line(Stream,Line),
%	(Line  \== end_of_file ->
%	((Line == [49,32] -> atom_concat(Name,'_1',ModulName), ModulContent=[]
%	;
%	read_from_codes(Line,Modul)),
%	Modul=modul(ModulName,ModulContent),
%modify to write ModulContent to file first then assert from that file.
%	open('temp_assert.pl',write,S1),
%	write(S1,ModulContent),write(S1,'.'),
%	close(S1),
%	open('temp_assert.pl',read,S2),
%	read_line(S2,L1),
%	(L1  \== end_of_file ->
%		read_from_codes(L1,M),
%		assert(Name:model(ModulName)),
%		asp:create_modul(ModulName,M);true),
%	close(S2),
%	absolute_file_name('$SHELL', Shell1),
%	process_create(Shell1, ['-c', ['rm -f ', 'temp_assert.pl']], [process(P1)]),
%	process_wait(P1,exit(0)),
%	read_from_stream(Stream,Name));read_from_stream(Stream,Name)).

%read_from_stream_first(Stream,Name):-
%	(at_end_of_stream(Stream) -> print('Unsatisfiable.\n'), fail,close(Stream) ; read_from_stream(Stream,Name)).
read_from_stream(Stream,Name):-
	( at_end_of_stream(Stream) -> true;
	%counting(X),	
	%X1 is X + 1,	
	%X < 500,
	%retractall(counting(_)),
	%assert(counting(X1)),
	%print(X),nl,
	read_line(Stream,Line),
	(Line  == end_of_file -> read_from_stream(Stream,Name);
	((Line == [49,32] -> atom_concat(Name,'_1',ModulName), ModulContent=[]
	;
	read_from_codes(Line,Modul)),
	Modul=modul(ModulName,ModulContent),
	assert(Name:model(ModulName)),
	asp:create_modul(ModulName,ModulContent),
	read_from_stream(Stream,Name)))).

read_from_stream_first(Stream,Name):-
	( at_end_of_stream(Stream) -> true;
	%counting(X),	
	%X1 is X + 1,	
	%X < 500,
	%retractall(counting(_)),
	%assert(counting(X1)),
	%print(X),nl,
	read_line(Stream,Line),
	(Line  == end_of_file -> print('Unsatisfiable.\n'),read_from_stream(Stream,Name);
	((Line == [49,32] -> atom_concat(Name,'_1',ModulName), ModulContent=[]
	;
	read_from_codes(Line,Modul)),
	Modul=modul(ModulName,ModulContent),
	assert(Name:model(ModulName)),
	asp:create_modul(ModulName,ModulContent),
	read_from_stream(Stream,Name)))).

 

check_skept_equil(P,[H|[]]):- H:P,!.
check_skept_equil(P,[H|T]):-
	H:P, check_skept_equil(P,T). 

show_dependency:-
	findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E),L1),
	print_depen(L1).

print_depen([P1|P]):-
	write(P1),nl,
	print_depen(P).

print_depen([]).

%-------------------------------to create arc-------------
retrieve_arc:-
	retractall(arc(_,_)),	
	findall(Module, scc_node(Module), ListModule),
	retrieve_arc(ListModule,ListModule).
retrieve_arc([],_).
retrieve_arc([Module|T],ListModule):-	
	findall(D, (dependency(Module,_,D,_,_,_), member(D,ListModule)), L1),
	remove_dups(L1,ListDepend),
	%write(ListDepend),%nl,
	create_arc(Module,ListDepend),
	retrieve_arc(T,ListModule).

create_arc(_,[]).

create_arc(M,[H|T]):-
	Term=.. ['arc',H,M],
	write(Term),nl,
	assert(Term),
	create_arc(M,T).

%-----------build strongly connected component using Tarjan algorithm

format_nodes([],Current,Final):-
    !, reverse_list(Current,Final).
format_nodes([H|T],Current,Final):- 
    retract(node(H,I,Lev,_,_)),
    format_nodes(T,[node(H,I,Lev)|Current],Final).


classify(X,Y,back):- 
    ( node(X,_,_,_,Anc) -> true ),
    ( node(Y,_,_,_,_) -> true ),
    member(Y,Anc).          
classify(X,Y,forward):- 
    ( node(X,_,_,_,_) -> true ),
    ( node(Y,_,_,_,Anc) -> true ),
    member(X,Anc).       
classify(_,_,cross).


format_arcs([],_,Final,Final):- !.
format_arcs([X|T],Scc,Current,Final):-
    retract(tree_arc(X,Y)),
    member(Y,Scc),             
    !, format_arcs([X|T],Scc,[arc(X,Y,tree)|Current],Final). 
format_arcs([X|T],Scc,Current,Final):-
    retract(arc(X,Y)),  
    member(Y,Scc),
    !, classify(X,Y,Class),         
    format_arcs([X|T],Scc,[arc(X,Y,Class)|Current],Final). 
format_arcs([_|T],Scc,Current,Final):-
    format_arcs(T,Scc,Current,Final).






partition1(N,[N|T],Current,[N|Current],T):- print(N),nl,!.
partition1(N,[H|T],Current,Final,Others):-
    print(N),nl,
    partition1(N,T,[H|Current],Final,Others).



form_scc1(Nodes,Arcs):-
    phigs(true),
    !, stream_for_c(W_stream),
    send_list_to_c(Nodes,W_stream),
    send_list_to_c(Arcs,W_stream).
form_scc1(_,_).


form_scc(N):-
    retract(visited(Nodes)),
    !, print(N),nl, partition1(N,Nodes,[],Scc,Others),
    assert(visited(Others)),
    format_arcs(Scc,Scc,[],L1),
    format_nodes(Scc,[],L2),
    print('scc(['),
    retractall(order1(_)),
    retract(scc1(SCC)),
    SCCNew is SCC + 1,
    assert(scc1(SCCNew)), 
    assert(order1(1)),
    writeq_utility(L1), write('],'), nl,
    write('['), writeq_utility1(L2),
    write(']).'), nl, nl,
    form_scc1(L2,L1).


/*-----------------------------------------------------------------------*/

reset_lowlink(N,H,lowlink):-
    ( node(N,_,_,N_Low,_) -> true ),
    ( node(H,_,_,H_Low,_) -> true ),
    N_Low > H_Low,
    !, retract(node(N,I,Lev,_,Anc)),
    assert(node(N,I,Lev,H_Low,Anc)).
reset_lowlink(N,H,index):-
    ( node(N,_,_,N_Low,_) -> true ),
    ( node(H,H_I,_,_,_) -> true ),
    N_Low > H_I,
    !, retract(node(N,I,Lev,_,Anc)),
    assert(node(N,I,Lev,H_I,Anc)).
reset_lowlink(_,_,_).




dfs(N,[],_):-
    ( node(N,Val,_,Val,_) -> true ),
    !, form_scc(N).
dfs(_,[],_):- !.          
dfs(N,[H|T],Lev):-
    retract(node(H,0)),    
    retract(arc(N,H)),
    !, assert(tree_arc(N,H)),  
    retract(visited(Nodes)),
    assert(visited([H|Nodes])),
    retract(index(I)),
    J is I + 1,
    assert(index(J)),
    H_Lev is Lev + 1,
    ( node(N,_,_,_,N_Anc) -> true ),    
    assert(node(H,J,H_Lev,J,[N|N_Anc])),    
    ( successors(H,S) -> true ),
    dfs(H,S,H_Lev),        
    reset_lowlink(N,H,lowlink), 
    dfs(N,T,Lev).
dfs(N,[H|T],Lev):-             
    !, reset_lowlink(N,H,index),   
    dfs(N,T,Lev).           
dfs(N,[_|T],Lev):-  
    dfs(N,T,Lev).       



/*-----------------------------------------------------------------------*/


depth_first_search:-
    retract(node(N,0)), 
    !, retract(index(I)),
    J is I + 1,
    assert(index(J)),
    assert(node(N,J,1,J,[])),  
    ( successors(N,S) -> true ),
    assert(visited([N])),   
    dfs(N,S,1),         
    retract(visited(_)),
    depth_first_search. 
depth_first_search.     


/*-----------------------------------------------------------------------*/

findall_successors(X,S):- 
    findall(Y,arc(X,Y),Z),      
    sort(Z,S).



prepare_nodes([]):- !.
prepare_nodes([H|T]):-
    assert(node(H,0)), 
    findall_successors(H,S),
    assert(successors(H,S)),
    prepare_nodes(T).


dfs_and_scc:-    
    findall(N,scc_node(N),Nodes),
    %retractall(node(_)),
    prepare_nodes(Nodes),
    assert(index(0)),       
    depth_first_search.

/*-----------------------------------------------------------------------*/
    

start:- assert(phigs(false)),    
    retractall(node_order(_,_)),
    retractall(scc(_)),
    retractall(order1(_)),
    retractall(scc1(_)),
    assert(scc1(0)),
    dfs_and_scc,                 
    retract(phigs(_)),      
    retractall(successors(_,_)),    
    retractall(node(_,_)),
    retractall(index(_)),
    retractall(scc(_,_)),
    retractall(node(_,_,_,_,_)),
    retractall(node(_,_,_)),
    retractall(visited(_)),
    retractall(scc(_)),
    retractall(tree_arc(_,_)), 
    retractall(arc(_,_)),   
    retractall(scc_node(_)).     
  


writeq_utility([]):- !.                
writeq_utility([H|[]]):- !, writeq(H).
writeq_utility([H|T]):- 
    writeq(H), write(','), nl, writeq_utility(T).

writeq_utility1([]):- !.                 
writeq_utility1([H|[]]):- !, writeq(H), scc1(SCC),retract(order1(N)), J is N + 1, assert(order1(J)), H = node(X,_,_), buildSCC(Y), (Y == 1 -> Term1=..['node_order',X,SCC,N];Term1=..['node_order_SCC',X,SCC,N]), assert(Term1).
writeq_utility1([H|T]):- 
    writeq(H), write(','), nl, scc1(SCC),retract(order1(N)), J is N + 1, assert(order1(J)), H = node(X,_,_), buildSCC(Y), (Y == 1-> Term1=..['node_order',X,SCC,N];Term1=..['node_order_SCC',X,SCC,N]), assert(Term1),
    writeq_utility1(T).

reverse_append([],L,L):- !.
reverse_append([X|L1],L2,L3):-
    reverse_append(L1,[X|L2],L3).

reverse_list(L1,L2):-
    reverse_append(L1,[],L2).

%----------------------------------------------------------------------assign order for each SCC.
%--------close stream
close_str :-
	findall(Z,current_stream(_,read,Z),ListZ),
	close_str1(ListZ).
close_str1([]).
close_str1([H|T]):-
	close(H),
	close_str1(T).

%-------------------build atoms true (1), false(2), or unknown(3).
get_equil(X):-
    statistics(walltime,[T_elapsed1,_]),
    findall(SCCorder,node_order(_,SCCorder,_), ListSCC),
    max_member(Max, ListSCC),
    %assert(scc_running(Max)),
    generate([],X,Max),
    print(X),nl,
    statistics(walltime,[T_elapsed2,_]),
    T is T_elapsed2 - T_elapsed1,
    print_statistics(T).
    %check(X).
generate(EQ,X1,Max):-
    %scc_running(R),
    Max \== 0,
    %retractall(scc_running(_)),
    NewMax is Max - 1,
    %assert(scc_running(Rnew)),    
    %print('R: '), %print(Max), %nl,
    findall(Node,node_order(Node,Max,_),ListNodeChecking),    
    generate_single_scc(EQ,ListNodeChecking, X),
    %print('single_scc: '), %print(X),nl,    
    generate(X,X2,NewMax),
    X1 = X2.

generate(EQ,X,NewMax):-
   %scc_running(R),
    %print('R: '), %print(NewMax), nl,
    NewMax == 0,
    X = EQ.


generate_single_scc(EQ,ListNode, X):-
    length(ListNode,Length),
    Length == 1, %%-strongly connected component has only one element
    generate_single(EQ,ListNode,X1),
    %print('generate single: '), %print(X1),%nl,
    keys_and_values(Output,ListNode,X1),
    append(EQ,Output,Newoutput),
    %print('Newoutput: '), %print(Newoutput),%nl,
    ListNode=[Node_check|_],
    check_newaddednode(Newoutput,Node_check),
    X = Newoutput.

generate_single_scc(EQ,ListNode, X):-
    length(ListNode,Length),
    \+ Length == 1, %%-strongly connected component has more than one element, try to break cycle.
    member(StartNode,ListNode),
    assert_scc_node(ListNode),
    print(StartNode),
    retractall(node_order_SCC(_,_,_)),
    retractall(arc(StartNode,_)),
    start,    %%check each new SCC has only one element or not, now assume it does
    findall(OrderInScc,node_order_SCC(_,OrderInScc,_), ListOrdersInSCC),
    max_member(Max, ListOrdersInSCC),
    generate_single_element_of_scc(EQ,X1,Max,[StartNode]),    
    %print('Newoutput111: '), %print(X1),%nl,
    %read(HEHE), print(HEHE), nl,
    findall(NodeChange,node_order_SCC(NodeChange,Max,_),ListNodeChange),
    check(X1,StartNode,ListNode,ListNodeChange),
    retract(this_ans(NewX)),    
    X = NewX.

generate_single_element_of_scc(EQ,X,Max,_):-
	Max == 0,
	X = EQ.
generate_single_element_of_scc(EQ,X1,Max,StartNode):-
	Max \== 0,
	NewMax is Max - 1,
	findall(Node,node_order_SCC(Node,Max,_),ListNodeChecking),
	generate_single(EQ,ListNodeChecking, X),
	%print('HEHEHEEE:'),%print(X), %nl,
	keys_and_values(EQ,ListNode1,AS1),	
	append(ListNode1,ListNodeChecking,ListNode2), 
	append(AS1, X, AS2),
	keys_and_values(NewOutput,ListNode2,AS2),  	  
   	check_with_ignored(NewOutput,StartNode,ListNodeChecking),
	generate_single_element_of_scc(NewOutput,X2, NewMax,StartNode),
	X1 = X2.

assert_scc_node([]):-
	retrieve_arc.
assert_scc_node([H|T]):-
	assert(scc_node(H)),
	assert_scc_node(T).

generate_single(_,[],[]):-!.
generate_single(De,[H|T],[H1|T1]):-        
    H:model(X),   
    list_predicate(X,Y),
    H1 = Y,    
    generate_single(De,T,T1).   	


check(X):-
    keys_and_values(X,ListNode,ListAS),    
    findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E, E=dependency(NodeChecked,_,_,_,_,_), member(NodeChecked,ListNode) ),L1),  
    check_each_dependence(L1,ListNode,ListAS).

check1(X):-
    keys_and_values(X,ListNode,ListAS),    
    findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E, E=dependency(NodeChecked,_,_,_,_,_), member(NodeChecked,ListNode) ),L1),  
    %trace,
    check_each_dependence(L1,ListNode,ListAS).

check_newaddednode(X,Node_check):-
    keys_and_values(X,ListNode,ListAS),    
    findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E, E=dependency(Node_check,_,_,_,_,_) ),L1),  
    %print('HELPHELPHELPHELPEHLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLL'),   
    check_each_dependence(L1,ListNode,ListAS).

check(X,CheckingNode,List_check):-    
    keys_and_values(X,ListNode,ListAS),    
    findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E, E=dependency(NodeChecked,_,CheckingNode,_,_,_), member(NodeChecked,List_check) ),L1),  
    check_each_dependence(L1,ListNode,ListAS).

check(X,CheckingNode,List_check,_):-    
    keys_and_values(X,ListNode,ListAS),    
    findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E, E=dependency(NodeChecked,_,CheckingNode,_,_,_), member(NodeChecked,List_check) ),L1),  
    check_each_dependence(L1,ListNode,ListAS),
    retractall(this_ans(_)),
    assert(this_ans(X)).

check(X,CheckingNode,List_check,List_changes):-    
    keys_and_values(X,ListNode,ListAS),    
    findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E, E=dependency(NodeChecked,_,CheckingNode,_,_,_), member(NodeChecked,List_check) ),L1),  
    \+ check_each_dependence(L1,ListNode,ListAS),
    List_changes = [NodeChanged],
    %trace,
    findall(Answer, (NodeChanged:model(Model), list_predicate(Model,Answer)), ListAnswer),
    member(Mem, ListAnswer),
    nth1(Order,ListNode,NodeChanged),
    nth1(Order,ListAS,AnswerNeedChanged),
    select(AnswerNeedChanged, ListAS, Mem, NewListAS),
    keys_and_values(NewX,ListNode,NewListAS),
    check(NewX),
    retractall(this_ans(_)),
    assert(this_ans(NewX)).    	
	

check_with_ignored(NewOutput,IgnoredNode,ListNodeChecking):-
    keys_and_values(NewOutput,ListNode,ListAS),    
    findall(E,(asp:current_predicate(dependency/6), functor(E,dependency,6), asp:E, E=dependency(Node,_,_,_,_,_),member(Node,ListNodeChecking) ),L1),  
    ignore_dependency(L1,IgnoredNode,L2),
    check_each_dependence(L2,ListNode,ListAS).
 
ignore_dependency(L1,[],L2):-
	L2 = L1.
ignore_dependency(L1,[H|T],L2):-	
	ignore_dependency1(L1,H,O1),	
	ignore_dependency(O1,T,L3),
	L2 = L3.

ignore_dependency1([],_,[]).
ignore_dependency1([H|T],A1,T1):-
	H = dependency(_,_,A1,_,_,_),
	ignore_dependency1(T,A1,T1).
ignore_dependency1([H|T],A1,[H1|T1]):-
	\+ H = dependency(_,_,A1,_,_,_),
	H1 = H,
	ignore_dependency1(T,A1,T1).

check_each_dependence([],_,_).
check_each_dependence([H|T],ListNode,ListAS):-
	H = dependency(X,Y,_,_,_,Num),
	%atom_concat(X,'___',X1),
	%atom_concat(X1,Y,X2),
	make_t_mcs(X,Y,X2),
	nth1(IndexNodeCheck,ListNode,X),
	nth1(IndexNodeCheck,ListAS,AS1),
	\+ member(X2,AS1),
	check_non_applicable([H|T],ListNode,ListAS),
	delete_dependency(T,X,Y,Num,T1),
	check_each_dependence(T1,ListNode,ListAS).

check_each_dependence([H|T],ListNode,ListAS):-
	H = dependency(X,Y,_,_,_,_),
	%atom_concat(X,'___',X1),
	%atom_concat(X1,Y,X2),
	make_t_mcs(X,Y,X2),
	nth1(IndexNodeCheck,ListNode,X),
	nth1(IndexNodeCheck,ListAS,AS1),
	member(X2,AS1),
	findall(Listnumber,dependency(X,Y,_,_,_,Listnumber),Listnum), %-- how many bridge rule has same X,Y.
	remove_dups(Listnum,RemovedListnum),
	length(RemovedListnum, Length),
	Length == 1,!,
	findall(Listnumber1,(asp:current_predicate(dependency/6),functor(Listnumber1,dependency,6), asp:Listnumber1, Listnumber1 = dependency(X,Y,_,_,_,_)),SameBR),	
	check_each_bridge(SameBR,ListNode,ListAS,Out),
	(Out=1 -> delete_dependency(T,X,Y,T1), check_each_dependence(T1,ListNode,ListAS);false).

check_each_dependence([H|T],ListNode,ListAS):-
	H = dependency(X,Y,_,_,_,_),
	%atom_concat(X,'___',X1),
	%atom_concat(X1,Y,X2),
	make_t_mcs(X,Y,X2),
	nth1(IndexNodeCheck,ListNode,X),
	nth1(IndexNodeCheck,ListAS,AS1),
	member(X2,AS1),
	%nth1(Index,ListNode,Z), 
	%nth1(Index,ListAS, AS),
	findall(Listnumber,dependency(X,Y,_,_,_,Listnumber),Listnum),
	remove_dups(Listnum,RemovedListnum),
	length(RemovedListnum, Length),
	\+ Length == 1,
	findall(Listnumber1,(asp:current_predicate(dependency/6),functor(Listnumber1,dependency,6), asp:Listnumber1, Listnumber1 = dependency(X,Y,_,_,_,_)),SameBR),	
	check_for_a_bridge(SameBR,ListNode,ListAS,Out),
	(Out=1 -> delete_dependency(T,X,Y,T1), check_each_dependence(T1,ListNode,ListAS); false).

check_non_applicable([H|T],ListNode,ListAS):-
	H = dependency(X,Y,_,_,_,N),	
	findall(Depend,(member(Depend,[H|T]), Depend=dependency(X,Y,_,_,_,N)),ListDepend),
	member(CheckingDepend, ListDepend),
	CheckingDepend = dependency(_,_,Z1,W1,M1,_),	
	nth1(Index,ListNode,Z1), 
	nth1(Index,ListAS, AS),
	(M1==1 -> \+ member(W1,AS); member(W1,AS)).
	
member_atom(X,Y):-
	convert_list(Y,Y1),
	atom_chars(X,X1),
	member(X1, Y1).

convert_list([],[]).
convert_list([H|T],[H1|T1]):-
	atom_chars(H,H1),
	change_list(T,T1).	

delete_dependency([],_,_,[]).
delete_dependency([H|T],X,Y,T1):-
	H = dependency(X,Y,_,_,_,_),
	delete_dependency(T,X,Y,T1).

delete_dependency([H|T],X,Y,[H1|T1]):-
	\+ H = dependency(X,Y,_,_,_,_),
	H1 = H,
	delete_dependency(T,X,Y,T1).

delete_dependency([],_,_,_,[]).
delete_dependency([H|T],X,Y,M,T1):-
	H = dependency(X,Y,_,_,_,M),
	delete_dependency(T,X,Y,M,T1).

delete_dependency([H|T],X,Y,M,[H1|T1]):-
	\+ H = dependency(X,Y,_,_,_,M),
	H1 = H,
	delete_dependency(T,X,Y,M,T1).
		
check_each_bridge([],_,_,Out):- Out=1.

check_each_bridge([H|T],ListNode,ListAS,Out):-
	H = dependency(_,_,Z,W,N,_),
	%atom_concat(X,'___',X1),
	%atom_concat(X1,Y,X2),
	%make_t_mcs(X,Y,X2),
	nth1(Index,ListNode,Z), 
	nth1(Index,ListAS, AS),
	(N == 1 ->  member(W,AS) ; \+ member(W,AS)), 
	check_each_bridge(T,ListNode,ListAS,Out).

check_each_bridge([H|_],ListNode,ListAS,Out):-
	H = dependency(_,_,Z,W,N,_),
	%atom_concat(X,'___',X1),
	%atom_concat(X1,Y,X2),
	%make_t_mcs(X,Y,X2),
	nth1(Index,ListNode,Z), 
	nth1(Index,ListAS, AS),
	\+ (N == 1 ->  member(W,AS) ; \+ member(W,AS)), 
	Out=0.  
 
check_for_a_bridge([],_,_,T):- T = 0.
check_for_a_bridge(SameBR,ListNode,ListAS,Output):-
	SameBR = [H|_],
	H = dependency(_,_,_,_,_,Num),
	findall(Listnumber1,(member(Listnumber1,SameBR), Listnumber1 = dependency(_,_,_,_,_,Num) ),Same),	
	check_each_bridge(Same,ListNode,ListAS,Out1),
	(Out1 == 1 -> Output = 1;delete(SameBR,dependency(_,_,_,_,_,Num),T1), check_for_a_bridge(T1,ListNode,ListAS,Out2),Output=Out2).

	   
%-----------finishing modifying by Tiep


%--------use_asp/1, use_asp/2: load models of file Name (parameters Paras) into List, store them in models_asp(Name,List)
use_asp_qa(C,S):-
	atom_concat(C,'.lp',Filename), 
 	atom_concat(C,'tmp',TmpFile), 

	absolute_file_name('$SHELL', Shell), 
	process_create(Shell, ['-c', ['cat ',S, '|sed -e \'/^user_/d\' -e \'/^description/d\' ',' > ',Filename]], [process(P1)]),
	process_wait(P1,exit(0)),

	file_exists(Filename),
	(on_exception(Err, compiledTMP(C), (Err = existence_error(_,_))) 
 	-> 
	cleanup_module(C),
	retractall(compiledTMP(C))
	;
	true),
	(file_exists(TmpFile) -> CompiledFile=TmpFile; CompiledFile=Filename),
	absolute_file_name('$SHELL', Shell), 
	process_create(Shell, ['-c', ['gringo ', ' ',' ', CompiledFile, '| clasp --opt-heu --opt-all | sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\'|sed -e =|sed -e \'N;s/\\n/ /\' -e \'s/ \\(.\\)/,\\1/g\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',C,'\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),
	read_line(Stream,Line), 
	Line  \== end_of_file,
	read_from_codes(Line,Modul),
	Modul=modul(ModulName,ModulContent),
	assert(C:model(ModulName)),
	assert(C:(model(X):-	Range=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
				asp:power_set(Range,Power_Set),
				member(_,Power_Set),
				\+ at_end_of_stream(Stream),
				read(Stream,L),	
				L=modul(X,C),
				assert(C:model(X)),
				asp:create_modul(X,C)			
				)),				
	create_modul(ModulName,ModulContent),
	assert(compiledTMP(C)).

use_asp(Name):-
	atom_concat(Name,'.lp',Filename), 
	atom_concat(Name,'tmp',TmpFile), 
	file_exists(Filename),
	(on_exception(Err, compiledTMP(Name), (Err = existence_error(_,_))) 
 	-> 
	cleanup_module(Name),
	retractall(compiledTMP(Name)),
	(file_exists(TmpFile) -> CompiledFile=TmpFile; CompiledFile=Filename)
	;
	CompiledFile=Filename,
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['rm -f ', TmpFile]], [process(P1)]),
	process_wait(P1,exit(0))),

	absolute_file_name('$SHELL', Shell), 
	process_create(Shell, ['-c', ['gringo ', ' ',' ', CompiledFile, '|clasp -n 0 --opt-heu --opt-all |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\'|sed -e =|sed -e \'N;s/\\n/ /\' -e \'s/ \\(.\\)/,\\1/g\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name,'\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),
	read_line(Stream,Line), 
	Line  \== end_of_file,
	read_from_codes(Line,Modul),
	Modul=modul(ModulName,ModulContent),
	assert(Name:model(ModulName)),
	assert(Name:(model(X):-	Range=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
				asp:power_set(Range,Power_Set),
				member(_,Power_Set),
				\+ at_end_of_stream(Stream),
				read(Stream,L),	
				L=modul(X,C),
				assert(Name:model(X)),
				asp:create_modul(X,C)			
				)),
				
	assert(Name:(skept(P):-	findall(X,Name:model(X),List),
				asp:check_skept(P,List)
				)),				
	create_modul(ModulName,ModulContent),
	assert(compiledTMP(Name)).

check_skept(P,[H|[]]):- H:P,!.
check_skept(P,[H|T]):-
	H:P, check_skept(P,T). 

use_asp(Name,Paras):-
	atom_concat(Name,'.lp',Filename),
	atom_concat(Name,'tmp',TmpFile),
	file_exists(Filename),
	name(Paras,CodeNumber),
	member(45,CodeNumber),
	(on_exception(Err, compiledTMP(Name), (Err = existence_error(_,_))) 
 	-> 
	cleanup_module(Name),
	retractall(compiledTMP(Name)),
	retractall(parasTMP(Name,_)),	
	(file_exists(TmpFile) -> CompiledFile=TmpFile; CompiledFile=Filename)
	;
	CompiledFile=Filename,
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['rm -f ', TmpFile]], [process(P1)]),
	process_wait(P1,exit(0))),

	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['gringo ', ' ',Paras,' ', CompiledFile, '|clasp -n 0 --opt-heu --opt-all |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\'|sed -e =|sed -e \'N;s/\\n/ /\' -e \'s/ \\(.\\)/,\\1/g\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name,'\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),
	read_line(Stream,Line), 
	Line  \== end_of_file,
	read_from_codes(Line,Modul),
	Modul=modul(ModulName,ModulContent),
	assert(Name:model(ModulName)),
	assert(Name:(model(X):-	Range=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
				asp:power_set(Range,Power_Set),
				member(_,Power_Set),
				\+ at_end_of_stream(Stream),
				read(Stream,L),	
				L=modul(X,C),
				assert(Name:model(X)),
				asp:create_modul(X,C)			
				)),				
	assert(Name:(skept(P):-	findall(X,Name:model(X),List),
				asp:check_skept(P,List)
				)),				
	create_modul(ModulName,ModulContent),
	assert(compiledTMP(Name)),
	asserta(parasTMP(Name,Paras)).

use_asp(Refname,Name):-
	atom_concat(Name,'.lp',Filename),
	atom_concat(Name,'tmp',TmpFile),
	file_exists(Filename),
	(on_exception(Err, compiledTMP(Refname), (Err = existence_error(_,_))) 
 	-> 
	cleanup_module(Refname),
	retractall(compiledTMP(Refname)),
	retractall(refTMP(Refname,Name)),
	(file_exists(TmpFile) -> CompiledFile=TmpFile; CompiledFile=Filename)
	;
	CompiledFile=Filename,
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['rm -f ', TmpFile]], [process(P1)]),
	process_wait(P1,exit(0))),

	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['gringo ', ' ',' ', CompiledFile, '| clasp -n 0 --opt-heu --opt-all |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\'|sed -e =|sed -e \'N;s/\\n/ /\' -e \'s/ \\(.\\)/,\\1/g\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Refname,'\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),
	read_line(Stream,Line), 
	Line  \== end_of_file,
	read_from_codes(Line,Modul),
	Modul=modul(ModulName,ModulContent),
	assert(Refname:model(ModulName)),
	assert(Refname:(model(X):-	Range=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
					asp:power_set(Range,Power_Set),
					member(_,Power_Set),
					\+ at_end_of_stream(Stream),
					read(Stream,L),	
					L=modul(X,C),
					assert(Refname:model(X)),
					asp:create_modul(X,C)			
					)),
	assert(Refname:(skept(P):-	findall(X,Refname:model(X),List),
					asp:check_skept(P,List)
					)),				
				
	create_modul(ModulName,ModulContent),
	assert(compiledTMP(Refname)),
	asserta(refTMP(Refname,Name)).

use_asp(Refname,Name,Paras):-
	atom_concat(Name,'.lp',Filename),
	atom_concat(Name,'tmp',TmpFile),
	file_exists(Filename),
	(on_exception(Err, compiledTMP(Refname), (Err = existence_error(_,_))) 
 	-> 
	cleanup_module(Refname),
	retractall(compiledTMP(Refname)),
	retractall(refTMP(Refname,Name)),
	retractall(parasTMP(Refname,_)),
	(file_exists(TmpFile) -> CompiledFile=TmpFile; CompiledFile=Filename)
	;
	CompiledFile=Filename,
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['rm -f ', TmpFile]], [process(P1)]),
	process_wait(P1,exit(0))),

	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['gringo ', ' ',Paras,' ', CompiledFile, '|clasp -n 0 --opt-heu --opt-all |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\'|sed -e =|sed -e \'N;s/\\n/ /\' -e \'s/ \\(.\\)/,\\1/g\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Refname,'\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),
	read_line(Stream,Line), 
	Line  \== end_of_file,
	read_from_codes(Line,Modul),
	Modul=modul(ModulName,ModulContent),
	assert(Refname:model(ModulName)),
	assert(Refname:(model(X):-	Range=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
					asp:power_set(Range,Power_Set),
					member(_,Power_Set),
					\+ at_end_of_stream(Stream),
					read(Stream,L),	
					L=modul(X,C),
					assert(Refname:model(X)),
					asp:create_modul(X,C)			
					)),
	assert(Refname:(skept(P):-	findall(X,Refname:model(X),List),
					asp:check_skept(P,List)
					)),				
				
	create_modul(ModulName,ModulContent),
	assert(compiledTMP(Refname)),
	asserta(refTMP(Refname,Name)),
	asserta(parasTMP(Refname,Paras)).

%--------bltg/2: the Pred belongs to some model(s) (of Name.lp) which also contains other Pred(s)
%--------if there exists bltg(Name,Pred) before in the program (credulous) 
bltg(Name,Pred) :-
%	model(Name,Model,_),
	(retract(existTPM(T,Name)) ->
	models_asp(Name,List),
	member(Model,List),
	member(Pred,Model),
	subset([Pred|T],Model),
	asserta(existTPM([Pred|T],Name))
	;
	models_asp(Name,List),
	member(Model,List),
	member(Pred,Model),
	subset([Pred],Model),
	asserta(existTPM([Pred],Name))).

%--------blth/3: the Pred belongs to the Number(th) model of the file Name.lp
blth(Name,Number,Pred) :-
	model(Name,Model,Number),
	member(Pred, Model).

%--------predicate bl/2: the Pred belongs to some models of file Name.lp (credulous)
bl(Name,Pred):-
	models_asp(Name,List),
	union(List, Union),
	member(Pred,Union).

%--------predicate bls/2: the Pred belongs to ALL models of file Name.lp (skeptical)
bl_s(Name,Pred) :-
	models_asp(Name,List),
	intersection(List, Intersection),
	member(Pred,Intersection).

%--------predicate model/3: the model Model is the Number(th) model of the file Name.lp
model(Name,Model,Number):-
	models_asp(Name,List),
%	length(List,N),
%	N >= Number,
	nth1(Number,List,Model).	

%--------predicate total_models/2: the total model of file Name.lp is Number
total_models(ModulName,Number):-
	findall(X,ModulName:model(X),List),
	length(List,Number).

%--------BEGIN:parse the models of file Name.lp into a list List--------%
%--------predicate load(Name,List), return models of file Name.lp into the list List, the elements are models
%load(Name,List) :-
%	absolute_file_name('$SHELL', Shell),
%	atom_concat(Name,'.lp',Filename), 
%	atom_concat(Name,'.tmp',Filenametmp), 
%	process_create(Shell, ['-c', ['lparse ', file(Filename), '|smodels 0 > ', Filenametmp]]),
%	sleep(0.02),
%	compile(Filenametmp),
%	parseAtoms(_,Listtmp1),
%	last(Listtmp1,L),
%	delete(Listtmp1, L, Listtmp2),
%	transform(Listtmp2, List),
%	process_create(Shell, ['-c', ['rm ', Filenametmp]]).

% -e \'/Answer/d\'
 
%stringasp1("sed -e '/^$/d' -e '/SATISFIABLE/d' -e '/OPTIMUM FOUND/d' -n -e '/^Answer/,/^Models/p' tmp > tmp1"). 
%stringasp2("sed -e '/Answer.*/d' -e '/Optimization.*/d' -e '/^Models/d' tmp1 > tmp2").

load(Name,List,Paras) :-
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['gringo ', ' ', Paras, ' ',Name,'|clasp -n 0 --opt-heu --opt-all |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\'']], [stdout(pipe(S1))]),

	set_input(S1),
	parseFile(Listtmp1),
	seen,
	transform(Listtmp1, List).
%	process_create(Shell, ['-c', ['rm tmp*']], [process(P5)]),
%	process_wait(P5,exit(0)).

parseFile(List):- 
	read_line(L), 
	(L  \== end_of_file
	->
	name(X,L), 
	add_element(X,List,List1), 
	parseFile(List1)
	;
	last(List,L1),
	delete(List,L1,_),
	!).

%--------predicate transfo rm/2: parse Listtmp2 into List (list of list), each element is a list containing a model
transform([Head|[]],List):-
	Head \== '',
	parseModels(Head,E1),
	add_element(E1,[],List).

transform([Head|Tail],List):-
	transform(Tail,L1),
	transform([Head|[]],L2),
	append(L2,L1,List).

%--------predicate parseModels/2 parse a string with blanks into a list, each element is a word in the string--------%
parseModels(Atom,List) :-
        splitModels(Atom,Atom1,Atom2),
        Atom2 \== '',
        parseModels(Atom2,List2),!,
	atom_concat(Atom1,'.',TMP),
	name(TMP,TMP1),
	read_from_codes(TMP1,TMP2),
        append([TMP2],List2,List).

parseModels(Atom,[TMP2]):- 
	on_exception(Err, atom_concat(Atom,'.',TMP), 
		    (Err = instantiation_error(_,_))), 
	name(TMP,TMP1),
	read_from_codes(TMP1,TMP2).	

splitModels(Atom,Atom1,Atom2) :-
	on_exception(Err, atom_length(Atom,Length), 
		    (Err = instantiation_error(_,_))), 
        name(Atom,List),
	nth1(P,List,32),
        P1 is P - 1,
        P2 is P,
        P3 is Length - P2,
	sub_atom(Atom,0,P1,_,Atom1),
	sub_atom(Atom,P2,P3,_,Atom2).

%--------END:parse the models of file Name.lp into a list List--------%
	
%--------predicate parseAtoms/2 parse the result/1 (from Filenametmp, loaded by compile(Filenametmp)) into Listtmp1--------%
%parseAtoms(Atom,List) :-
%        splitAtom(Atom,Atom1,Atom2),
%        Atom2 \== ' ',
%	abolish(result/1),
%	call(assertz(result(Atom2))),
%        parseAtoms(Atom2,List2),!,
%        append([Atom1],List2,List),
%	abolish(result/1).

%parseAtoms(Atom,[Atom]).

%splitAtom(Atom,Atom1,Atom2) :-
%	result(Atom),
%        atom_length(Atom,Length),
%        name(Atom,List),
%	nth1(P,List,64),
%        P1 is P - 2,
%        P2 = P,
%        P3 is Length - P2,
%	sub_atom(Atom,0,P1,_,Atom1),
%	sub_atom(Atom,P2,P3,_,Atom2).

%-------------------------------------------------------------------
parseAtoms1(Atom,List) :-
        splitAtom1(Atom,Atom1,Atom2),
        Atom2 \== '',
        parseAtoms1(Atom2,List2),!,
        append([Atom1],List2,List).

parseAtoms1(Atom,[Atom]).

splitAtom1(Atom,Atom1,Atom2) :-
        atom_length(Atom,Length),
        name(Atom,List),
	nth1(P,List,44),
        P1 is P - 1,
        P2 is P,
        P3 is Length - P2,
	sub_atom(Atom,0,P1,_,Atom1),
	sub_atom(Atom,P2,P3,_,Atom2).

parseAtoms2(Atom,List) :-
        splitAtom2(Atom,Atom1,Atom2),
        Atom2 \== '',
        parseAtoms2(Atom2,List2),!,
        append([Atom1],List2,List).

parseAtoms2(Atom,[Atom]).

splitAtom2(Atom,Atom1,Atom2) :-
        atom_length(Atom,Length),
        name(Atom,List),
	nth1(P,List,124),
        P1 is P - 1,
        P2 is P,
        P3 is Length - P2,
	sub_atom(Atom,0,P1,_,Atom1),
	sub_atom(Atom,P2,P3,_,Atom2).

transform1([Head|[]],List):-
	Head \== '',
	parseAtoms2(Head,E1),
	add_element(E1,[],List).

transform1([Head|Tail],List):-
	transform1(Tail,L1),
	transform1([Head|[]],L2),
	append(L2,L1,List).

model(Modul,Model):-
	current_predicate(_,Modul:Model).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%--------predicate appendDB/2: append Pred to file Name.lp
/*
appendDB(Name,Pred):-
	atom_concat(Name,'.lp',Filename), 
%	atom_concat(Pred,'.',Pred1), 
	open(Filename, append, S),
	write(S, Pred),
	write(S, '.'),
	nl(S),
	close(S),
	E=[a,Filename,Pred],
	call(asserta(updateTMP(E))),
	retract(models_asp(Name,_)),
	(on_exception(Err, parasTMP(Name,Paras), (Err = existence_error(_,_))) 
 	-> use_asp(Name,Paras)
	;
%	modeTMP(Name,Mode),
	use_asp(Name)).

%--------predicate removeDB/2: remove Pred from file Name.lp
removeDB(Name,Pred):-
	absolute_file_name('$SHELL', Shell),
	atom_concat(Name,'.lp',Filename),
	atom_concat(Name,'.tmp',Filenametmp),
	String =  '\\',
	atom_concat(Pred,String,Pred1),
	process_create(Shell, ['-c', ['sed -e "/', Pred1,'./d" ', Filename, ' >', Filenametmp ]], [process(P1)]),
	process_wait(P1,exit(0)),
	process_create(Shell, ['-c', ['mv ', Filenametmp, ' ', Filename]], [process(P2)]),
	process_wait(P2,exit(0)),
	E1=[r,Filename,Pred],
	call(asserta(updateTMP(E1))),
	retract(models_asp(Name,_)),
	(on_exception(Err, parasTMP(Name,Paras), (Err = existence_error(_,_))) 
 	-> use_asp(Name,Paras)
	;
%	modeTMP(Name,Mode),
	use_asp(Name)).

%--------undo updates happened before (append and remove)
backtrack :-
	retract(updateTMP(E)),
	(nth1(1,E,'a') ->
	nth1(2,E,Filename),
	nth1(3,E,Pred),
	absolute_file_name('$SHELL', Shell),
	atom_concat(Filename,'.tmp',Filenametmp),
	String =  '\\',
	process_create(Shell, ['-c', ['sed -e "/', Pred, String,'./d" ', Filename, ' >', Filenametmp ]], [process(P1)]),
	process_wait(P1,exit(0)),
	process_create(Shell, ['-c', ['mv ', Filenametmp, ' ', Filename]],[process(P2)]),
	process_wait(P2,exit(0))	
	;
	(nth1(1,E,'r') ->
	nth1(2,E,Filename),
	nth1(3,E,Pred),
	atom_concat(Pred,'.',Pred1), 
	open(Filename, append, S),
	nl(S),
	write(S, Pred1),
	close(S))),
	atom_concat(Name,'.lp',Filename),
	retract(models_asp(Name,_)),
	(on_exception(Err, parasTMP(Name,Paras), (Err = existence_error(_,_))) 
 	-> use_asp(Name,Paras)
	;
%	modeTMP(Name,Mode),
	use_asp(Name)).
*/	
%--------END:append, remove and backtrack from database--------%

/*
%--------The Model is one of models of the module Modul
Modul>>Model :-
	models_asp(Modul,List),
%	random_permutation(List,L),
	member(Model,List).

%--------The E is the element that belongs to ALL models of the module Modul
Modul::s(E) :-
	bl_s(Modul,E).

%--------The E is the element that belongs to SOME models of the module Modul
Modul::c(E) :-
	bl(Modul,E).

%--------The E is an element of the model Model 
Model::E :-
	member(E,Model).

%--------Delete models of Modul s.t not contain E 
Modul::assertInt(E) :-
	models_asp(Modul,List),
	include(member(E),List,S),
%	asserta(models_asp_backup(Modul,List)),
%	asserta(models_asp_lasttime(Modul,S)),
	retractall(models_asp(Modul,_)),
	asserta(models_asp(Modul,S)).
*/
%--------Restore models of file Modul which was changed by Modul::assertInt(E)
%restoreModel(Modul):-
%	retractall(models_asp(Modul,_)),
%	models_asp_backup(Modul,LM),
%	asserta(models_asp(Modul,LM)).

%--------keep the models of Modul before they are changed at point I (I is an interger)
%lastState(Modul,I):-
%	models_asp(Modul,List),
%	asserta(lasttime(Modul,List,I)).
	
%--------restore the models of Modul which were changed at point I (I is an interger)
%restore_point(I):-
%	\+ atomic(lasttime(_,_,I)).
%restore_point(I):-
%	findall([Modul,List],lasttime(Modul,List,I),L),
%	retractall(lasttime(_,_,I)),
%	I1 is I+1,
%	I2 is I+2,
%	I3 is I+3,
%	retractall(lasttime(Modul,_,I1)),
%	retractall(lasttime(Modul,_,I2)),
%	retractall(lasttime(Modul,_,I3)),
%	recover(L).
%recover([]).
%recover(L):-
%	L=[[C,D]|T],
%	retractall(models_asp(C,_)),
%	asserta(models_asp(C,D)),
%	recover(T).

%find_plan(Name,I,N):-
%	I<N+1,
%	It is I+48,
%	char_code(Atom,It),
%	atom_concat('-c length=',Atom,Paras),	
%	(use_asp(Name,Paras)
%	->
%	write('Stop at step = '),write(I)
%	;
%	I1 is I+1,
%	find_plan(Name,I1,N)).

% :-call(asserta(lasttime(temp,temp,10000))).
%--------load models of file Name into List, store them in models_asp(Name,List)
%use_asp(Name):-
%	(retractall(models_asp(Name,List)) ->
%	load(Name,List),
%	asserta(models_asp(Name,List))
%	;
%	load(Name,List),
%	asserta(models_asp(Name,List))).
	
%use_asp(Name,Paras,Mode):-
%	(retractall(models_asp(Name,_)), 	
%	retractall(parasTMP(Name,_)),
%	retractall(modeTMP(Name,_))
%	->
%	load(Name,List,Paras),
%	asserta(models_asp(Name,List)),
%	asserta(parasTMP(Name,Paras)),
%	asserta(modeTMP(Name,Mode))
%	;
%	load(Name,List,Paras),
%	asserta(models_asp(Name,List)),
%	asserta(parasTMP(Name,Paras))),
%	asserta(modeTMP(Name,Mode)).

%import('t1,plan_A|-c length=4')

%import(List):-
%	transform1(List,L1),	
%	process(L1).

%belong(Name,Pred):-
%	modeTMP(Name,Mode),
%	Mode == 's' ->
%	bl_s(Name,Pred).

%belong(Name,Pred):-
%	modeTMP(Name,Mode),
%	Mode == 'c' ->
%	bltg(Name,Pred).

%for_loop(Start,End,Inc,Action) :-
%	(var(Start) -> Start = 1,
%	(End >= Start,
%	NewValue is Start+Inc,
%	(Action -> for_loop(NewValue,End,Inc,Action)))
%	;
%	(End >= Start,
%	NewValue is Start+Inc,
%	(Action -> for_loop(NewValue,End,Inc,Action)
%	))).

%bls(Name,Pred) :-
%	models_asp(Name,List),
%	length(List,N),
%	for_loop(Start,N,1, member(Pred,nth1(Start,List,Model))).	


%bl(Name,Pred):-
%	models_asp(Name,List),
%	length(List,N),
%	between(1,N,Number),
%	nth1(Number,List,Model),
%	member(Pred, Model).

%bls(Name,Pred):-
%	models_asp(Name,List),
%	length(List,N),
%	between(1,N,Number),
%	nth1(Number,List,Model),
%	\+ member(Pred, Model), !,
%	fail.
%bls(_,_):- true.
%--------import(S) will import all ASP modules including in string S: 'Name1|Paras1,Name2|Paras2...'
%import(S):-
%	parseAtoms1(S,L), 
%	transform1(L,L1),	
%	process(L1).

%process([]).

%process([H|T]):-
%	length(H,Number),
%	(Number == 1
%	->
%	nth1(1,H,Name),
%	use_asp(Name)
%	;
%	nth1(1,H,Name),
%	nth1(2,H,Paras),
%	use_asp(Name,Paras)),
%	process(T).	

%% load_MCS(ListOfFiles,ListOfModules,ListOfOutputFiles)
%% load_MCS(['a43.pl','a43.asp'],[a43pl,a43asp],[asp1,asp2]).

load_MCS([],[],[]).

load_MCS([P|T],[P1|T1],[P2|T2]):-
        process_MCS(P,P1,P2),
	load_MCS(T,T1,T2). 

process_MCS(P,P1,P2):-
	% read the file 
	% replace bridge rule with new 
	%atom_concat(P1,'_asp',PN),
	retractall(dependency_number(_)),	
	assert(dependency_number(0)), %--for building dependency.	
	process_MCS1(P,P1,P2).
	
process_MCS1(Filename,Module,OutputFile):-
	retractall(activeModule(_)),
	retractall(bridge_num(_)),
	assert(bridge_num(0)),
	assert(activeModule(Module)),
	process(Filename,X),!,	
	split_1_char(X,'.',L),
	preprocess(L,X1),
	preprocess_remove_add_space(X1,X2),
	write_asp(X2,OutputFile,Module).
	
%solve_asp applied for DCOP which is always adding file.add in solving. For normal case, remove Hehe
solve_asp_models_in_fact(ListOfASPModules,OutputModule):-
	open(OutputModule,write,Stream_temp),
	write_modules_to_stream(ListOfASPModules,Stream_temp),
	close(Stream_temp),
	absolute_file_name('$SHELL', Shell),
	%process_create(Shell, ['-c', ['rm -f ', TmpFile]], [process(P1)]),
	%process_wait(P1,exit(0))),
	%create_asp(Name,ASPFile),
	%absolute_file_name('$SHELL', Shell1),
	atom_concat(OutputModule,'.add',Hehe),
	atom_concat(OutputModule,'.asp',Hehe1),
	atom_concat(OutputModule,'.table',Hehe2),
	atom_concat('model_',OutputModule,Name1),
	process_create(Shell, ['-c',  ['gringo ', ' ',' ', OutputModule,  ' ', Hehe,' ', Hehe1, ' ', Hehe2, ' | clasp | sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\' -e \'/Optimization/d\' -e \'/OPTIMUM/,$d\' | sed -e "s/ \\(.\\)/,\\1/g"  -e \'s/$/ /\'  | sed -e = | sed -e \'N;s/\\n/ /\' -e \'s/ /,/\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name1,'_\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),!,
	read_from_stream_first(Stream,OutputModule),
	%print('hahaha=====after.\n'),
	assert(OutputModule:(skept(P):-	findall(X,OutputModule:model(X),List),
				asp:check_skept(P,List)
				)),			
	close(Stream),	
	write('heel'),write(compiledTMP(OutputModule)),nl.
	%process_create(Shell, ['-c', ['rm -f ', OutputModule]], [process(P1)]),
	%process_wait(P1,exit(0)).

solve_asp_models_in_fact_already_prepared(ListOfASPModules,OutputModule):-	
	absolute_file_name('$SHELL', Shell),
	 
	atom_concat(OutputModule,'.add',Hehe),
	atom_concat(OutputModule,'.asp',Hehe1),
	 
	atom_concat('model_',OutputModule,Name1),
	 
	process_create(Shell, ['-c',  ['gringo ', ' ',' ', OutputModule,  ' ', Hehe,' ', Hehe1, ' | clasp | sed -n \'/Answer/,$p\' |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\' -e \'/Optimization/d\' -e \'/OPTIMUM/,$d\' | sed -e "s/ \\(.\\)/,\\1/g"  -e \'s/$/ /\'  | sed -e = | sed -e \'N;s/\\n/ /\' -e \'s/ /,/\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name1,'_\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),!,
	read_from_stream_first(Stream,OutputModule),
	%print('hahaha=====after.\n'),
	assert(OutputModule:(skept(P):-	findall(X,OutputModule:model(X),List),
				asp:check_skept(P,List)
				)),			
	close(Stream).	
	%write('heel'),write(compiledTMP(OutputModule)),nl.
	%process_create(Shell, ['-c', ['rm -f ', OutputModule]], [process(P1)]),
	%process_wait(P1,exit(0)).

%%-----------------------------------------------------------------
%%solve asp to get only answerset where input is a string specifies files input.


solve_asp_models_given_stringfiles(StringInputFileList,OutputModule):-
	absolute_file_name('$SHELL', Shell),	
	%atom_concat(OutputModule,'.add',Hehe),
	%atom_concat(OutputModule,'.asp',Hehe1),	
	atom_concat('model_',OutputModule,Name1),		
	process_create(Shell, ['-c',  ['gringo ', ' ' , StringInputFileList, ' ' , ' | clasp | sed -n \'/Answer/,$p\' |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\' -e \'/Optimization/d\' -e \'/OPTIMUM/,$d\' | sed -e "s/ \\(.\\)/,\\1/g"  -e \'s/$/ /\'  | sed -e = | sed -e \'N;s/\\n/ /\' -e \'s/ /,/\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name1,'_\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),!,

	read_from_stream_first(Stream,OutputModule),
	%print('hahaha=====after.\n'),
	assert(OutputModule:(skept(P):-	findall(X,OutputModule:model(X),List),
				asp:check_skept(P,List)
				)),			
	close(Stream).	
	%write('heel'),write(compiledTMP(OutputModule)),nl.
	%process_create(Shell, ['-c', ['rm -f ', OutputModule]], [process(P1)]),
	%process_wait(P1,exit(0)).

%%-----------------solve_asp_to_get_only_answerset_where_input_is_files

solve_asp_models_given_files(InputFileList,OutputModule):-
	prepare_input_file_list(InputFileList,StringOutPut),	
	absolute_file_name('$SHELL', Shell),	
	InputFileList=[File],
	atom_concat(File,'.asp',Hehe),	
	atom_concat(File,'.table',Table),
	%atom_concat(OutputModule,'.add',Hehe),
	%atom_concat(OutputModule,'.asp',Hehe1),	
	atom_concat('model_',OutputModule,Name1),		
	process_create(Shell, ['-c',  ['gringo ', ' ',' ', StringOutPut, ' ' , Hehe, ' ' , File, ' ' , Table, ' | clasp | sed -n \'/Answer/,$p\' |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\' -e \'/Optimization/d\' -e \'/OPTIMUM/,$d\' | sed -e "s/ \\(.\\)/,\\1/g"  -e \'s/$/ /\'  | sed -e = | sed -e \'N;s/\\n/ /\' -e \'s/ /,/\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name1,'_\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),!,

	read_from_stream_first(Stream,OutputModule),
	%print('hahaha=====after.\n'),
	assert(OutputModule:(skept(P):-	findall(X,OutputModule:model(X),List),
				asp:check_skept(P,List)
				)),			
	close(Stream).	
	%write('heel'),write(compiledTMP(OutputModule)),nl.
	%process_create(Shell, ['-c', ['rm -f ', OutputModule]], [process(P1)]),
	%process_wait(P1,exit(0)).

solve_asp_models_given_list_files(InputFileList,OutputModule):-
        prepare_input_file_list(InputFileList,StringOutPut),
        absolute_file_name('$SHELL', Shell),
        %InputFileList=[File],
        %atom_concat(File,'.asp',Hehe),
        %atom_concat(File,'.table',Table),
        %atom_concat(OutputModule,'.add',Hehe),
        %atom_concat(OutputModule,'.asp',Hehe1),
        atom_concat('model_',OutputModule,Name1),
        process_create(Shell, ['-c',  ['gringo ', ' ',' ', StringOutPut, '  | clasp | sed -n \'/Answer/,$p\' |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\' -e \'/Optimization/d\' -e \'/OPTIMUM/,$d\' | sed -e "s/ \\(.\\)/,\\1/g"  -e \'s/$/ /\'  | sed -e = | sed -e \'N;s/\\n/ /\' -e \'s/ /,/\' -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name1,'_\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),!,

        read_from_stream_first(Stream,OutputModule),
        %print('hahaha=====after.\n'),
        assert(OutputModule:(skept(P):- findall(X,OutputModule:model(X),List),
                                asp:check_skept(P,List)
                                )),
        close(Stream).
        %write('heel'),write(compiledTMP(OutputModule)),nl.
        %process_create(Shell, ['-c', ['rm -f ', OutputModule]], [process(P1)]),
        %process_wait(P1,exit(0)).

prepare_input_file_list([],' ').
prepare_input_file_list([H|T],StringOutPut):-
	prepare_input_file_list(T,StringOutPut1),
	atom_concat(H, ' ' , H1),
	atom_concat(H1, StringOutPut1,StringOutPut).

%%%%%%-------------------------------------------------------------------------------------------

%solve_asp_models_in_string	
solve_asp(ListOfASPModules,OutputModule):-
	open(OutputModule,write,Stream_temp),
	write_modules_to_stream(ListOfASPModules,Stream_temp),
	close(Stream_temp),
	absolute_file_name('$SHELL', Shell),
	%process_create(Shell, ['-c', ['rm -f ', TmpFile]], [process(P1)]),
	%process_wait(P1,exit(0))),
	%create_asp(Name,ASPFile),
	%absolute_file_name('$SHELL', Shell1),
	atom_concat(OutputModule,'.add',Hehe),
	%print('hehehehehehe-------before.\n'),
	process_create(Shell, ['-c', ['gringo ', ' ',' ', OutputModule, ' ', Hehe,' |clasp | grep UNSATIS | sed "s/^/\'/" |  sed -e \'s/$/ /\' -e "s/ /\'./" | sed \'s/UNSATISFIABLE/fail/\' ']], [stdout(pipe(Stream1))]),!,
	(test_unsatisfy(Stream1,OutputModule) -> print('fail'),fail,close(Stream1) ;
	%print('hehehehehe------true after.\n'),
	close(Stream1),
	atom_concat('model_',OutputModule,Name1),
	%absolute_file_name('$SHELL', Shell), 
	%print('hahahah======before.\n'),	
	process_create(Shell, ['-c', ['gringo ', ' ',' ', OutputModule, ' ', Hehe, ' |clasp | sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\' -e \'/Optimization/d\' -e \'/OPTIMUM/,$d\' | sed -e "s/ \\(.\\)/\',\'\\1/g" -e \'s/$/ /\' -e "s/ /\'/" | sed -e = | sed -e \'N;s/\\n/ /\' -e "s/ /,\'/" -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',Name1,'_\\1,[\\2])./\' ']], [stdout(pipe(Stream))]),!,
	read_from_stream_first(Stream,OutputModule),
	%print('hahaha=====after.\n'),
	assert(OutputModule:(skept(P):-	findall(X,OutputModule:model(X),List),
				asp:check_skept(P,List)
				)),			
	close(Stream),	
	write('hehelo'),write(compiledTMP(OutputModule)),nl,
	process_create(Shell, ['-c', ['rm -f ', OutputModule]], [process(P1)]),
	process_wait(P1,exit(0))).
	
write_modules_to_stream([],_).
write_modules_to_stream([H|T],Stream):-
	write_module_to_stream(H,Stream),
	write_modules_to_stream(T,Stream).

write_module_to_stream(H,Stream):-
	findall(Rule,H:ruleLP(Rule),Rules),
	write_rules_to_stream(Rules,Stream).
	
write_rules_to_stream([],_).
write_rules_to_stream([H|T],Stream):-
	write(Stream,H), write(Stream,'.\n'),
	write_rules_to_stream(T,Stream).
%------------------------------------------------------------------------------------------	
negotiate([],X,X1):-
	X1 = X.
negotiate([H|T],X,Output):-
	update(H,X),!,
	%help(HELP),
	%HELP1 is HELP + 1,
	%assert(help(HELP1)),
	%atom_chars(H,H1),
	%append(Name1,['_','a','s','p'],H1),
	%atom_chars(Name,Name1),
	read_File(H,' ',Stream),
	%help(HELP),	
	readOneModel(Stream,ModulContent),
	append([X,ModulContent],X1),
	negotiate(T,X1,Output).

update(H,X):-
	atom_concat(H,'.lp',Filename),	
	open(Filename,write,Stream),
	atom_chars(H,H1),
	append(Name1,['_','a','s','p'],H1),
	atom_chars(Name,Name1),
	write_rule(Name,Stream),
	write_negotiate(Name,X,Stream),
	%make_redunt(Stream),
	close(Stream).
	
write_rule(Name,Stream):-
	findall(X,Name:ruleLP(X),ListRules),
	write_rule1(ListRules,Stream).

write_rule1([],_):-!.
write_rule1([H|T],Stream):-
	write(Stream,H),
	%write(Stream,'.'),
	nl(Stream),
	write_rule1(T,Stream).

write_negotiate(Name,X,Stream):-
	findall(Atom,dependency(Name,_,p1,Atom,_,_),ListAtom),
	write_negotiate1(ListAtom,X,Stream).

write_negotiate1([],_,_).
write_negotiate1([H|T],X,Stream):-
	member(H,X),
	atom_concat('p1___',H,Atom1),
	write(Stream,Atom1),write(Stream,'.'),nl(Stream),
	write_negotiate1(T,X,Stream).
write_negotiate1([H|T],X,Stream):-
	\+ member(H,X),
	atom_concat('p1___',H,Atom1),
	write(Stream,':- '),write(Stream,Atom1),write(Stream,'.'),nl(Stream),
	write_negotiate1(T,X,Stream).
	

compute_MCS([], _,_). 

compute_MCS(ListProgs, ListNames,X):-
	write('here'), 
	assert(help(0)),
	assert(help(1)),
	assert(help(2)),
	assert(help(3)),
	assert(help(4)),
	assert(help(5)),
	assert(help(6)),
	assert(help(7)),
	assert(help(8)),
	assert(help(9)),
	assert(help(10)),
	assert(help(11)),
	assert(help(12)),
	load_MCS(ListProgs, ListNames),!,
	%trace,
	negotiate(ListNames,[],X). 

read_File(File,FileExtra,Stream):-	
	atom_concat('model_',File,File1),	
	atom_concat(File,'_asp.lp',ASPFileInput),
	absolute_file_name('$SHELL', Shell),
	process_create(Shell, ['-c', ['gringo ', ' ',' ', ASPFileInput, '  ', FileExtra ,'  | clasp | grep UNSATIS | sed "s/^/\'/" |  sed -e \'s/$/ /\' -e "s/ /\'./" | sed \'s/UNSATISFIABLE/fail/\' ']], [stdout(pipe(Stream1))]),
	(test_unsatisfy(Stream1,File) -> print('fail'),close(Stream1),fail ; 
	print('true'),close(Stream1), 
	process_create(Shell, ['-c', ['gringo ', ' ',' ', ASPFileInput, '  ', FileExtra ,' | clasp -n 0 |sed -e \'/Answer/d\' -e \'/SATISFIABLE/,$d\' -e \'/Optimization/d\' -e \'/OPTIMUM/,$d\' | sed -e "s/ \\(.\\)/\',\'\\1/g" -e \'s/$/ /\' -e "s/ /\'/" | sed -e = | sed -e \'N;s/\\n/ /\' -e "s/ /,\'/" -e \'s/\\([[:alnum:]]*\\),\\(.*\\)/modul(',File1,'_\\1,[\\2])./\' ']], [stdout(pipe(Stream))])).

readOneModel(Stream,Model,Name):-
	( at_end_of_stream(Stream) ->	false;	
	read_line(Stream,Line),
	(Line == end_of_file -> false ;
	(Line == [49,32] -> atom_concat(Name,'_1',ModulName), Model=[]	;
	read_from_codes(Line,Modul), 
	Modul=modul(ModulName,Model)))). %end  of Line == [49,32]
	
%test(Stream,Model,Success):-
%	repeat, 
%	(at_end_of_stream(Stream) -> Success = fail, Model = [],true; 
%	    readOneModel(Stream,Model),
%	    isAGoodModel(Model)), Success = true,!. 

isAGoodModel(Model):-
	write(Model), nl, 
	true.
		
compatible(ListOfProgs, Answer) :- 
	compatible(ListOfProgs, [], Answer). 
	
compatible([], Answer, Answer):-
            open('sol.txt',write,S),
            write(S,Answer),
            close(S).

compatible([Prog | List], Temp, Answer):-
	update_X(Prog, Temp, NProg),
	read_File(Prog,NProg,Stream),	
	repeat, 
	(at_end_of_stream(Stream) -> Success = fail, Model = [],true; 
	    readOneModel(Stream,Model,Prog),
	    %isAGoodModel(Model)), %Success = true, 
	    keys_and_values(NewPair, [Prog], [Model]),	   
	    append(Temp, NewPair, NewTemp),	   
	    compatible(List, NewTemp, Answer),
	    Success = true),
	!,
	(Success == true -> true; false).
 	%clingo Prog + NProg 
	%read_on_model M  
	%check for compatible of M with Temp 
	%if good: add M to Temp and continue with compatible(List, Temp, Answer) 
	%else .....



update_X(Prog, Temp, NProg):-
	keys_and_values(Temp, Keys, Values),
	atom_concat(Prog,'_qs.lp', NProg),
	open(NProg,write,Stream),
	update_q1(Keys, Values, Prog, Stream),
	update_q2q3(Keys, Values, Prog, Stream),	
	close(Stream).

update_q1([],[],_,_):-!.
update_q1([H|T], [H1|T1], Prog, Stream):-
	process_q1(H,H1,Prog,Stream),
	update_q1(T,T1,Prog,Stream).

process_q1(H,H1,Prog,Stream):-
	findall(Atom,dependency(H,_,Prog,Atom,_,_) ,ListAtom),
	write_q1(ListAtom, H1, Prog, Stream).

write_q1([],_,_,_):-!.
write_q1([H|T], H1, Prog, Stream):-
	%atom_concat(Prog,'___', Prog1),
	%atom_concat(Prog1,H,Tnp),
	make_t_mcs(Prog, H, Tnp),
	(member(Tnp, H1) -> 
	  write(Stream, ':- not '), write(Stream, H), write(Stream,'.'), nl(Stream) ;
	  true),
	write_q1(T,H1,Prog,Stream).




update_q2q3([],[],_,_):-!.
update_q2q3([H|T], [H1|T1], Prog, Stream):-
	process_q2q3(H,H1,Prog,Stream),
	update_q2q3(T,T1,Prog,Stream).

process_q2q3(H,H1,Prog,Stream):-
	findall(Atom,dependency(Prog,_,H,Atom,_,_) ,ListAtom),
	write_q2q3(ListAtom, H1, H, Stream).

write_q2q3([],_,_,_):-!.
write_q2q3([H|T], H1, Prog, Stream):-	
	%atom_concat(Prog,'___', Prog1), 
	%atom_concat(Prog1,H,Tip),
	make_t_mcs(Prog, H, Tip),
	(member(H, H1) -> 
	  write(Stream, Tip), write(Stream,'.'), nl(Stream) ;
	  write(Stream,':- '), write(Stream, Tip), write(Stream,'.'), nl(Stream) ),
	write_q2q3(T,H1,Prog,Stream).




