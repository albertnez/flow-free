% prolog flow solver
% Albert Martinez

% Our variables: 
% col-I-J-C - square(I,J) has color C
% s-I-J-X-Y - the successor of square(I,J) is square(X,Y)
% d-I-J-N   - cell I-J is at distance N from the begin of path
%
:-include(input/entradaFlow9).
:-include(displayFlow). 
:-dynamic(varNumber/3).
symbolicOutput(0). % set to 1 to see symbolic output only; 0 otherwise.
countCombinations(0). % 1 to get num solutions, 0 to get min length solution.
drawAllSolutions(1). % set to 1 to generate all solutions when counting them.

:-dynamic(ladderId/1).
ladderId(0).
:-dynamic(solutionId/1).
solutionId(0).

% Colors
isColor(X):- c(X, _, _, _, _).

% Upper bound of the max length
getMaxLength(L):-
  findall(X, isColor(X), C),
  size(M),
  length(C, N),
  L is M*M - 2*(N-1).

isLength(L):-
  isMaxLength(M),
  between(0, M, L).

isRow(X):-
  size(N),
  between(1,N,X).

% (I, J) is adjacent to (X, Y)
isAdjacent(I,J,X,Y):-
  I is X-1, isRow(I), J is Y.
isAdjacent(I,J,X,Y):-
  I is X+1, isRow(I), J is Y.
isAdjacent(I,J,X,Y):-
  J is Y-1, isRow(J), I is X.
isAdjacent(I,J,X,Y):-
  J is Y+1, isRow(J), I is X.

writeClauses:-
  writeInitialValues,
  writeOneSuccessor,
  writeIsSuccessor,
  writeColorPerCell,
  writeSuccessorColor,
  % These two are not needed, they are implicit in the length propagation
  %writeNotCycles, 
  %writePathImplication,
  writeLengthPropagation,
  writeMaxLength,
  writeOneLengthPerCell.


% Write the colors of the being and end points
writeInitialValues:-
  c(C, II, IJ, EI, EJ),
  writeClause([col-II-IJ-C]),
  writeClause([col-EI-EJ-C]),
  writeClause([d-II-IJ-0]), % the init has length 0
  % End will have no successor
  isAdjacent(AI,AJ,EI,EJ),
  writeClause([\+s-EI-EJ-AI-AJ]), % TODO perhaps remove  this
  fail.
writeInitialValues.


% Every cell has to have exactly one successor, except endpoints
writeOneSuccessor:-
  isRow(I), isRow(J), % for each cell
  \+c(_,_,_,I,J), % can't be endpoints
  findall(s-I-J-AI-AJ, isAdjacent(AI,AJ,I,J), C), % each adjacent cell
  writeEO(C),
  fail.
writeOneSuccessor.

% Every cell must be the successor of only one, except begin
writeIsSuccessor:-
  isRow(I), isRow(J),
  \+c(_,I,J,_,_),
  findall(s-AI-AJ-I-J, isAdjacent(AI,AJ,I,J), C),
  writeEO(C),
  fail.
writeIsSuccessor.


% Every cell has to have exactly one color
writeColorPerCell:-
  isRow(I), isRow(J),
  findall(col-I-J-C, isColor(C), X),
  writeEO(X),
  fail.
writeColorPerCell.

% Successors should have same color
% suc-I-J-AI-AJ ^ col-I-J-C -> col-AI-AJ-C
% p ^ q -> r  = (!p v !q) v r
writeSuccessorColor:-
  isRow(I), isRow(J),
  isAdjacent(AI,AJ,I,J),
  isColor(C),
  writeClause([\+s-I-J-AI-AJ, \+col-I-J-C, col-AI-AJ-C]),
  fail.
writeSuccessorColor.

%%%%%% reach clause %%%%%%
% To avoid extra cycles. This is no longer neededwhen doing the length
% propagation
/*
writeNotCycles:-
  isRow(I), isRow(J),
  writeClause([\+r-I-J-I-J]),
  fail.
writeNotCycles.
  
% Propagation of reach
writePathImplication:-
  isRow(I), isRow(J),
  isAdjacent(AI,AJ,I,J),
  writeClause([\+s-I-J-AI-AJ, r-I-J-AI-AJ]),
  isRow(OI), isRow(OJ),
  writeClause([\+s-I-J-AI-AJ, \+r-OI-OJ-I-J, r-OI-OJ-AI-AJ]),
  fail.
writePathImplication.
*/
%%%%%% end reach clause %%%%

%%%%% length clauses %%%%%%
writeOneLengthPerCell:-
  isRow(I), isRow(J),
  findall(d-I-J-L, isLength(L), C),
  writeEO(C),
  fail.
writeOneLengthPerCell.

% Propagation of length
writeLengthPropagation:-
  isRow(I), isRow(J),
  isAdjacent(AI,AJ,I,J),
  isLength(L),
  isMaxLength(ML),
  L < ML,
  NL is L+1,
  writeClause([\+s-I-J-AI-AJ, \+d-I-J-L, d-AI-AJ-NL]),
  fail.
writeLengthPropagation.

% Clause limiting the length
writeMaxLength:-
  isMaxLength(L),
  isRow(I), isRow(J),
  writeClause([\+d-I-J-L]),
  fail.
writeMaxLength.
%%%%% end length clause %%%%%%

%%%%% NUMBER OF SOLUTIONS  %%%%%
writeNotPreviousSolutions(L):- % L is a list of lists
  member(X, L), % for each list of clauses, print ALO of them
  writeALO(X),
  fail.
writeNotPreviousSolutions(_).

writeCombinationClauses(L):-
  writeInitialValues,
  writeOneSuccessor,
  writeIsSuccessor,
  writeColorPerCell,
  writeSuccessorColor,
  writeLengthPropagation,
  writeOneLengthPerCell,
  writeMaxLength,
  writeNotPreviousSolutions(L).

% Get all successor clauses that are true
getCombinationClauses([], []).
getCombinationClauses(L, [P|M]):-
  num2var(P,s-X1-Y1-X2-Y2),
  getCombinationClauses(L2, M),
  append([\+s-X1-Y1-X2-Y2], L2, L). % Negated clause of successor
getCombinationClauses(L, [_|M]):-
  getCombinationClauses(L, M).

% If drawAllSolutions option is enabled, draw all solutions
displaySolutionIfNeeded(M):-
  drawAllSolutions(1),
  retract(solutionId(Id)),
  NewId is Id + 1,
  assert(solutionId(NewId)),
  displaySolWithFilename(M, Id).
displaySolutionIfNeeded(_).

treatCombinationsSolution(0, [], _). % Unsat, 0 combinations
treatCombinationsSolution(X, M, L):- % There is solution
  displaySolutionIfNeeded(M),
  getCombinationClauses(Clauses, M),
  append([Clauses], L, L2),
  numCombinations(Num, L2),
  X is Num + 1.
  
% Number of combinations having seen the ones in L
numCombinations(X, L):-
  resetVars,
	tell(clauses), writeCombinationClauses(L), told,
	tell(header),  writeHeader,  told,
	unix('cat header clauses > infile.cnf'),
	unix('picosat -v -o model infile.cnf'),
  %unix('cat model'),
	see(model), readModel(M), seen, 
  treatCombinationsSolution(N, M, L),
  X is N.

%%%%% END NUMBER OF SOLUTIONS %%%%%


%%%%% AUX CLAUSE FUNCTIONS %%%%%
% Write exactly one, using at least one, and at most one
writeEO(L):- writeALO(L), writeAMO(L).

% Write at least one, just put all literals in the same clause
writeALO(L):- writeClause(L).

% Write at most one, write all negated pairs in a clause each
/*
writeAMO(L):-
  append( _,[X|L1],L), member(Y,L1), 
  writeClause([\+X, \+Y]),
  fail.
writeAMO(_).
*/
writeAMO(L):-
  writeAMOLadder(L).

% Write an at most one with ladder encoding.
%Variabes auxiliares a_i que significan: "uno de x_1...x_i es cierto".
%Para cada i tenemos clausulas:
   %x_i ->  a_i                                    -x_i v  a_i   
   %a_i -> -x_i+1    que en forma clausal son:     -a_i v -x_i+1
   %a_i ->  a_i+1                                  -a_i v  a_i+1
writeAMOLadder([P|L]):-
  retract(ladderId(Id)),
  NewId is Id + 1,
  assert(ladderId(NewId)),
  Aux = aux-Id-0,
  writeLadderClauses(L, Id, 1, P, Aux).
  
writeLadderClauses([], _, _, LastLit, LastAux):-
  writeClause([\+LastLit, LastAux]).

writeLadderClauses([Lit|L], Id, Ind, LastLit, LastAux):-
  NewInd is Ind+1,
  Aux = aux-Id-NewInd,
  writeClause([\+LastLit, LastAux]),
  writeClause([\+LastAux, \+Lit]),
  writeClause([\+LastAux, Aux]),
  writeLadderClauses(L, Id, NewInd, Lit, Aux).
%%%%% End Ladder %%%%%

% Reset all vars, except max length
resetVars:-
  retractall(numClauses(_)), assert(numClauses(0)),
  retractall(numVars(_)), assert(numVars(0)),
  retractall(varNumber(_,_,_)),
  retractall(num2var(_,_)),
  retractall(color(_,_,_)).


%%%%%%% MIN LENGTH %%%%%%%%%%%
getMaxLengthFound(0, []).
getMaxLengthFound(ML, [P|M]):-
  num2var(P,d-_-_-D),
  getMaxLengthFound(ML2, M),
  ML is max(D, ML2).
getMaxLengthFound(ML, [_|M]):-
  getMaxLengthFound(ML, M).

treatSolution([], L):-
  write('No solution found with max length '), write(L), nl.
treatSolution(M, _):-
  displaySol(M),
  getMaxLengthFound(ML, M),
  write('Found solution with length '), write(ML), write('.'), nl,
  L2 is ML-1,
  solveWithMaxLength(L2).
treatSolution(_,_).

solveWithMaxLength(0). % Not possible
solveWithMaxLength(L):-
  % Reset all variables
  resetVars,
  retractall(isMaxLength(_)), assert(isMaxLength(L)),

  write('Trying to solve with max length '), write(L), write('...'), nl,
	tell(clauses), writeClauses, told,
	tell(header),  writeHeader,  told,
	unix('cat header clauses > infile.cnf'),
	unix('picosat -v -o model infile.cnf'),
  %unix('cat model'),
	see(model), readModel(M), seen, 
  treatSolution(M, L).
%%%%%%%%% END MIN LENGTH %%%%%%%%%%%

% ========== No need to change the following: =====================================

main:- symbolicOutput(1), !, writeClauses, halt. % escribir bonito, no ejecutar
main:-
  countCombinations(1),
  write('Counting the number of different solutions...'), nl,
  getMaxLength(L),
  assert(isMaxLength(L)),
  numCombinations(X, []),
  write('The number of different solutions is: '), write(X), nl,
  halt.
main:-  
  countCombinations(0),
  write('Finding the solution with longest path being minimal...'), nl,
  getMaxLength(L),
  solveWithMaxLength(L),
  halt.

var2num(T,N):- hash_term(T,Key), varNumber(Key,T,N),!.
var2num(T,N):- retract(numVars(N0)), N is N0+1, assert(numVars(N)), hash_term(T,Key),
	assert(varNumber(Key,T,N)), assert( num2var(N,T) ), !.

writeHeader:- numVars(N),numClauses(C),write('p cnf '),write(N), write(' '),write(C),nl.

countClause:-  retract(numClauses(N)), N1 is N+1, assert(numClauses(N1)),!.
writeClause([]):- symbolicOutput(1),!, nl.
writeClause([]):- countClause, write(0), nl.
writeClause([Lit|C]):- w(Lit), writeClause(C),!.
w( Lit ):- symbolicOutput(1), write(Lit), write(' '),!.
w(\+Var):- var2num(Var,N), write(-), write(N), write(' '),!.
w(  Var):- var2num(Var,N),           write(N), write(' '),!.
unix(Comando):-shell(Comando),!.
unix(_).

readModel(L):- get_code(Char), readWord(Char,W), readModel(L1), addIfPositiveInt(W,L1,L),!.
readModel([]).

addIfPositiveInt(W,L,[N|L]):- W = [C|_], between(48,57,C), number_codes(N,W), N>0, !.
addIfPositiveInt(_,L,L).

readWord(99,W):- repeat, get_code(Ch), member(Ch,[-1,10]), !, get_code(Ch1), readWord(Ch1,W),!.
readWord(-1,_):-!, fail. %end of file
readWord(C,[]):- member(C,[10,32]), !. % newline or white space marks end of word

readWord(Char,[Char|W]):- get_code(Char1), readWord(Char1,W), !.
%========================================================================================

