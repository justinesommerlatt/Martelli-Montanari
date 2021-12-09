% operateur ?=
:- op(20,xfy,?=).

% PREDICATS D AFFICHAGE FOURNIS DANS LE SUJET

% set_echo : lance l affichage par le predicat echo
set_echo :- assert(echo_on).

% clr_echo : empeche l afichage par le predicat echo
clr_echo :- retractall(echo_on).

% echo(T) : affiche le terme T si le flag echo_on est positionne, sinon ne renvoie rien
echo(T) :- echo_on, !, write(T).
echo(_).



% PREDICATS POUR APPLIQUER LES regles

% RENOMMAGE D UNE VARIABLE
% regles(X?=T,rename) : renvoie true si T est une variable
regles(X?=T,rename) :- var(X),var(T),!.

% SIMPLIFICATION DE CONSTANTE
% regles(X?=A,simplify) : renvoie true si A est une constante, si X est une constante alors x==a (x et a sont identiques)
regles(X?=A,simplify) :- var(X),atomic(A),!;atomic(X),atomic(A),X==A,!.

% UNIFICATION D UNE VARIABLE AVEC UN TERME COMPOSE
% regles(X?=T,expand) : renvoie true si T est compose et X n apparait pas dans T
regles(X?=T,expand) :- var(X),compound(T),\+occur_check(X,T),!.

% DECOMPOSITION DE DEUX FONCTIONS
% regles(X?=T,decompose) : renvoie true ssi X et T ont le meme symbole ET le meme nombre d arguments
regles(X?=T,decompose) :- compound(X),compound(T),functor(X,N,A),functor(T,M,B),N==M,A==B,!.

% GESTION DE CONFLIT ENTRE DEUX FONCTIONS
% regles(X?=T,clash) : renvoie true si X et T n ont pas le meme symbole OU pas le meme nombre d arguments
regles(X?=T,clash) :- compound(X),compound(T),functor(X,N,A),functor(T,M,B),(N \== M ; A \== B),!.

% VERIFICATION DE PRESENCE D OCCURRENCE
% regles(X?=T,check) : renvoie true si X\==T (X est différent de T) et X apparait dans T 
regles(X?=T,check) :- var(X),X\==T,!,occur_check(X,T).

% ECHANGE
% regles(X?=T,orient) : renvoie true si T n est pas une variable
regles(T?=X,orient) :- var(X),nonvar(T),!.

% TEST D OCCURRENCE
occur_check(V,T) :- var(T),T==V,!.
occur_check(V,T) :- compound(T),arg(_,T,X),occur_check(V,X),!.


% APPLICATION DES PREDICATS DEFINIS

% RENOMMAGE D UNE VARIABLE
% application(rename,x?=t,x?=t|p,q) : renomme les occurrences de x en la variable t 
application(rename,X?=T,P,Q) :- X=T,Q=P.

% ECHANGE
% application(orient,t?=x,t?=x|p,q) : permute le t avec le x
application(orient,T?=X,P,Q) :- append([X?=T],P,Q).

% SIMPLIFICATION DE CONSTANTE
% application(simplify,x?=a,x?=a|p,q) : renomme les occurrences de x en la constante t
application(simplify,X?=T,P,Q) :- X=T,Q=P.

% UNIFICATION D UNE VARIABLE AVEC UN TERME COMPOSE
% application(expand,x?f(v),x?=f(v)|p,q) : renommes les occurrences de x en terme compose f(v)
application(expand,X?=T,P,Q) :- X=T,Q=P.

% DECOMPOSITION DE DEUX FONCTIONS
% application(decompose,f(x)?=f(y),f(x)?=f(y)|p,q) : decompose l equation
application(decompose,X?=T,P,Q) :- X=..XT,new_list(XT,XL),T=..TT,new_list(TT,TL),croisement(XL,TL,S),append(S,P,Q).

% GESTION DE CONFLIT ENTRE DEUX FONCTIONS
%inutile car si absence de clause == fail
application(clash,_,_,_) :- fail.

% occurrence
%inutile car si absence de clause == fail
application(check,_,_,_) :- fail.

% REDUCTION DE SYSTEME D EQUATIONS EN UN AUTRE SYSTEME D EQUATIONS
% Transforme le systeme d equations P en systeme d equations Q en appliquant la regles de transformation R a l equation E
% reduit(R,E,P,Q) : renvoie true si la regle est applicable
reduit(R,E,P,Q) :- \+regles(E,clash), \+regles(E,check),regles(E,R),aff_regle(R,E),!,application(R,E,P,Q).


unifie([A|P]) :- aff_sys([A|P]),reduit(_,A,P,Q),!,unifie(Q).
unifie([]) :- echo('\n Il n’y a plus d’équation à unifier, unification terminée\n').

% choix premier([E|P],Q,E,R) : selectionne la premiere equation du systeme afin de la resoudre
choix_premier([E|P],Q,E,R) :- reduit(R,E,P,Q),!.

% choix_pondere([E|P],Q,E,R) : selectionne la regles avec le poids le plus eleve afin de l'appliquer
choix_pondere(P,Q,E,R) :- choix_eq(P,Q,E,R,[]),!.

% choix_alea(P,Q,E,R) : choix aleatoire AUTRE STRATEGIE POSSIBLE
% choix_alea(P,Q,E,R) :-length(P,A), C is random(A)+1,arg(C,P,G),reduit(R,G,P,Q),!.

% unifie(P,S) : regles appliquant l unification de P selon la regles donnee (choix_premier ou choix_pondere)
unifie([E|P],choix_premier) :- aff_sys([E|P]),choix_premier([E|P],Q,E,_),!,unifie(Q,choix_premier).
unifie([E|P],choix_pondere) :- aff_sys([E|P]),choix_pondere(P,Q,E,_),!,unifie(Q,choix_pondere).

% unifie([E|P],choix_alea) :- aff_sys([E|P]),choix_alea([E|P],Q,E,_),!,unifie(Q,choix_alea).
unifie([],_) :- echo('\nUnification terminée.\n\nRésultat :\n').

% DESACTIVE L AFFICHAGE
unif(P,S) :- clr_echo,unifie(P,S).

% ACTIVE L AFFICHAGE
trace_unif(P,S) :- set_echo,unifie(P,S).

% initialisation lancement du programme
:- initialization main.

main :- write('\n\n\n\nAlgorithme d\'unification de Martelli_Montanari\n\n'),
		write('L\'affichage des traces d\'exécution est activé par défaut si vous saisissez unifie(P,S)\n\n'),
		write('Pour désactiver l\'affichage et exécuter sans aucune trace d\'unification, saisir unif(P,S).\n\n'),
		write('Pour réactiver l\'affichage et exécuter avec traces d\'exécution, saisir trace_unif(P,S).\n\n'),
		write('P est un système d\'équation de type [X?=Y,f(G)?=Z]\n'),
		write('S est la stratégie souhaitée : choix_premier ou choix_pondere\n\n\n\n'),
		set_echo.
		


% PREDICATS ANNEXES


% new_list(A,B) : transforme une liste en une autre liste en gardant uniquement le reste
new_list([_|P],XL) :- XL=P.


% croisement(A,B,C) : prend deux a deux les elements de chaque liste afin d en faire une liste de type [A?=B,...]
croisement([A|P],[B|Q],S) :- croisement(P,Q,Z),append([A?=B],Z,S).
croisement([],[],S) :- S=[].

% clash,check>rename,simplify>orient>decompose>expand
% N correspond a l ordre de priorite avec priorite 1 > priorite 2 donc on fait la regles de priorite 1 avant la regles de priorite 2 
choix_regle(E,R,N) :- regles(E,clash) -> R='clash',N=1,!;
						regles(E,check) -> R='check',N=2,!;
							regles(E,rename) -> R='rename',N=3,!;
								regles(E,simplify) -> R='simplify',N=4,!;
									regles(E,orient) -> R='orient',N=5,!;
										regles(E,decompose) -> R='decompose',N=6,!;
											regles(E,expand) -> R='expand',N=7,!.
											
% choix_eq(P,Q,E,R,S) : compare deux a deux les equations et recupere l equation comportant la regles a appliquer en priorite
choix_eq([A|P],Q,E,R,S) :- choix_regle(E,RE,CE),choix_regle(A,_,CA),CE=<CA,append([A],S,L),choix_eq(P,Q,E,_,L), R=RE, ! ;
						   choix_regle(E,_,CE),choix_regle(A,RA,CA),CA<CE,append([E],S,L),choix_eq(P,Q,A,_,L),R=RA.
choix_eq([],Q,E,R,L)	:- var(R),choix_regle(E,R,_),aff_regle(R,E),application(R,E,L,Q),!;
						   nonvar(R),aff_regle(R,E),application(R,E,L,Q).
						   

% PREDICATS POUR L AFFICHAGE
aff_sys(P) :- echo('system: '),echo(P),echo('\n').
aff_regle(R,E) :- echo(R),echo(': '),echo(E),echo('\n').








				

