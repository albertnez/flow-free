% Esto es una pista: aqui se supone que hay variables:
%    s-X-Y-A-B que dicen que el sucesor de la casilla X-Y es A-B
%    col-X-Y-C que dicen que el color de la casilla X-Y es C
% pero puede haber otras variables...

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rgb( blue,         0,   0 ,    1).
rgb( brown,     0.72, 0.53,  0.4).
rgb( red,          1,    0,    0).
rgb( cyan,         0,    1,    1).
rgb( green,        0,  0.5,    0).
rgb( yellow,       1,    1,    0).
rgb( pink,         1, 0.75,  0.8).
rgb( violet,    0.54, 0.17, 0.89).
rgb( orange,       1, 0.55,    0).
rgb( darkblue,     0,    0, 0.55).
rgb( darkgreen,    0, 0.39,    0).
rgb( darkred,   0.55,    0,    0).
rgb( darkcyan,     0, 0.55, 0.55).
rgb( white,      0.9,  0.9,  0.9).
rgb( grey,       0.5,  0.5,  0.5).
%% added colors
rgb( black,        0,    0,    0).
rgb( lightgreen, 0.5,    1,  0.5). 
rgb( lightblue, 0.20, 0.27,    1).



writeHeaderPS:-
    writeln('%!PS'),
    writeln('matrix currentmatrix /originmat exch def'),
    writeln('/umatrix {originmat matrix concatmatrix setmatrix} def'),
    writeln('[28.3465 0 0 28.3465 10.5 100.0] umatrix').

writeGrid:-
    writeln('0.01 setlinewidth'),
    writeVertGrid,
    writeHorizGrid.

writeVertGrid:-
    size(R), size(C), C1 is C+1,
    between(1,R,I), between(1,C1,J), drawVertical(I,J),fail.
writeVertGrid.

writeHorizGrid:-
    size(R), size(C), R1 is R+1,
    between(1,R1,I), between(1,C,J), drawHorizontal(I,J),fail.
writeHorizGrid.

drawVertical(I,J):-
    size(R),size(C),
    Size is min(22/R,18/C),
    X is 1+(J-1)*Size,
    Y is 23-(I-1)*Size,
    write(X), write(' '), write(Y), write(' moveto'),nl,
    Y1 is Y-Size,
    write(X), write(' '), write(Y1), write(' lineto'),nl,
    writeln('stroke').

drawHorizontal(I,J):-
    size(R),size(C),
    Size is min(22/R,18/C),
    X is 1+(J-1)*Size,
    Y is 23-(I-1)*Size,
    write(X), write(' '), write(Y), write(' moveto'),nl,
    X1 is X+Size,
    write(X1), write(' '), write(Y), write(' lineto'),nl,
    writeln('stroke').

writeInits:-
    c(C,X1,Y1,X2,Y2),
    writeInit(X1,Y1,C),
    writeInit(X2,Y2,C),
    fail.
writeInits.

writeInit(I,J,K):-
    size(R),size(C),
    Size is min(22/R,18/C),
    X is 1+(J-1)*Size +   Size/2,
    Y is 23-(I-1)*Size -  Size/2,
    Radius is Size/8,
    write(X), write(' '), write(Y), write(' '), write(Radius), writeln(' 0 360 arc'),
    writeln('gsave'),
    rgb(K,Red,Green,Blue),
    write(Red), write(' '), write(Green), write(' '), write(Blue), write(' setrgbcolor'),nl,
    writeln('fill'),
    writeln('grestore'),
    writeln('0.01 setlinewidth'),
    writeln('stroke').

writeSolution([X|M]):-
    writeLine(X),
    writeSolution(M).
writeSolution([]).

assertColors([]).
assertColors([X|L]):-
    num2var(X,col-I-J-K),!,
    assert(color(I,J,K)),
    assertColors(L).
assertColors([_|L]):-
    assertColors(L).
    
writeLine(P):-
    num2var(P,s-X1-Y1-X2-Y2),!,
    size(R),size(C),
    color(X1,Y1,K),
    color(X2,Y2,K), % small typo here!. changed color(X1,Y2,K).
    Size is min(22/R,18/C),
    X is 1+(Y1-1)*Size + Size/2,
    Y is 23-(X1-1)*Size - Size/2,
    XF is 1+(Y2-1)*Size + Size/2,
    YF is 23-(X2-1)*Size - Size/2,
    rgb(K,Red,Green,Blue),
    writeln('0.11 setlinewidth'),
    write(Red), write(' '), write(Green), write(' '), write(Blue), write(' setrgbcolor'),nl,
    write(X), write(' '), write(Y), write(' moveto'),nl,
    write(XF), write(' '), write(YF), write(' lineto'),nl,
    writeln('stroke').
writeLine(_).

displaySol(M):-
    tell('graph.ps'),
    writeHeaderPS,
    writeGrid,
    writeInits,
    assertColors(M),
    writeSolution(M),
    writeln('showpage'),
    told.

% Write a solution with name 'graph-Id.gs'
displaySolWithFilename(M, Id):-
    term_to_atom(Id, Atom),
    atom_concat('graph-', Atom, Name),
    atom_concat(Name, '.gs', Filename),
    tell(Filename),
    writeHeaderPS,
    writeGrid,
    writeInits,
    assertColors(M),
    writeSolution(M),
    writeln('showpage'),
    told.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
