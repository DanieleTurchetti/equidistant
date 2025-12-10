---------------------Program 1----------------

R = ZZ/7
S = R[e1,e2,e3,e4][W,Y,Z,X,T]

I=ideal(-e3*X+e4*Y,e2*X-e3*Y+e4*Z,-e1*X+e2*Y-e3*Z+e4*W, X-e1*Y+e2*Z-e3*W+e4*T)
gens gb(I)
G = gens gb(I)
G_0
-------------------------
R = ZZ/5
S = R[e1,e2,e3,e4][Y,Z,X]

I=ideal(-e3*X+e4*Y,e2*X-e3*Y+e4*Z)
gens gb(I)
G = gens gb(I)
G_0
------------
R = ZZ/11
S = R[e1,e2,e3,e4][Y1,Y2,Y3,Y4,Y5,Y6,Y7,X,Z]

I=ideal(-e3*X+e4*Y1,e2*X-e3*Y1+e4*Y2,-e1*X+e2*Y1-e3*Y2+e4*Y3, X-e1*Y1+e2*Y2-e3*Y3+e4*Y4, Y1-e1*Y2+e2*Y3-e3*Y4+e4*Y5, Y2-e1*Y3+e2*Y4-e3*Y5+e4*Y6, Y3-e1*Y4+e2*Y5-e3*Y6+e4*Y7, Y4-e1*Y5+e2*Y6-e3*Y7+e4*Z)
gens gb(I)
G = gens gb(I)
G_0


---------------------Program 2----------------

------------------useful functions---------

weightList = n -> (
    if n < 2 then error "n must be at least 2";
    L = apply(n, i -> if i == 0 or i == n-1 then 0 else 1);
    L)

addLinRel = (I,S) -> (
    varsList := gens S;  -- list of variables in the ring
    k := #varsList;      -- number of variables
    newGens = for i from 0 to k-5 list (
        varsList_i
        - e1*varsList_(i+1)
        + e2*varsList_(i+2)
        - e3*varsList_(i+3)
        + e4*varsList_(i+4)
    );
    I + ideal newGens)


---The aim is to solve the linear system and then express the last variable as a function of the first one
---Then, the degree in e_2 is computed, as well as the two highest coefficients, showing that e1=e3=0 in each case.
---------------p=5-----------------

R = ZZ/5
S = R[e1,e3,e4][e2][a .. f, MonomialOrder=>{Weights => weightList(6)}]

I = ideal(-e3*a+e4*b,e2*a-e3*b+e4*c,-e1*a+e2*b-e3*c+e4*d);
J = addLinRel(I,S)

G = gens gb(J)
G_0_0
degree(G_0_0)_a
((G_0_0)_a)_(e2^2)
((G_0_0)_a)_e2

-------------p=7--------------------

R = ZZ/7

S = R[e1,e3,e4][e2][a .. j, MonomialOrder=>{Weights => weightList(10)}]
I = ideal(-e3*a+e4*b,e2*a-e3*b+e4*c,-e1*a+e2*b-e3*c+e4*d);
J = addLinRel(I,S)

G = gens gb(J);
G_0_0
degree(G_0_0)_a
((G_0_0)_a)_(e2^4)
((G_0_0)_a)_(e2^3)

-----------p=11-----------------------

R = ZZ/11
S = R[e1,e3,e4][e2][a .. r, MonomialOrder=>{Weights => weightList(18)}]
I = ideal(-e3*a+e4*b,e2*a-e3*b+e4*c,-e1*a+e2*b-e3*c+e4*d);
J = addLinRel(I,S)


G = gens gb(J);
G_0_0
degree(G_0_0)_a
((G_0_0)_a)_(e2^8)
((G_0_0)_a)_(e2^7)

---------------------Program 3----------------

--In this part we compute N_j(p) and N_j(1).

weightList = n -> (
    if n < 2 then error "n must be at least 2";
    L = apply(n, i -> if i == 0 or i == n-1 then 0 else 1);
    L)

addRel = (I,S) -> (
    varsList := gens S;  
    k := #varsList;     
    newGens = for i from 0 to k-3 list (
        varsList_i
        + e2*varsList_(i+1)
        + e4*varsList_(i+2)
    );
    I + ideal newGens)

---------------p=5, W1-----------------

R = ZZ/5
S = R[e4][e2][a .. d, MonomialOrder=>{Weights => weightList(4)}]

J = addRel(e2*a+e4*b,S);

G = gens gb(J)
G_0_0

---------------p=7, W1-----------------

R = ZZ/7
S = R[e4][e2][a .. f, MonomialOrder=>{Weights => weightList(6)}]

J = addRel(e2*a+e4*b,S);

G = gens gb(J)
G_0_0

---------------p=7, W2-----------------

R = ZZ/7
S = R[e4][e2][a .. c, MonomialOrder=>{Weights => weightList(3)}]

J = addRel(e2*a+e4*b,S);

G = gens gb(J)
G_0_0

---------------p=11, W1-----------------

R = ZZ/11
S = R[e4][e2][a .. j, MonomialOrder=>{Weights => weightList(10)}]

J = addRel(e2*a+e4*b,S);

G = gens gb(J)
G_0_0

---------------p=11, W2-----------------

R = ZZ/11
S = R[e4][e2][a .. e, MonomialOrder=>{Weights => weightList(5)}]

J = addRel(e2*a+e4*b,S);

G = gens gb(J)
G_0_0

---------------Here we verify that hat(W1) has simple roots-------------
---------------NB. Fraction fields over polynomial rings in positive characteristic are not supported, hence the need to work with homogeneous forms-----

---------p=5-------

R = ZZ/5
S = R[a,e2,e4][Y,Z][j]
W1 = Z^3-2*e4*Z*Y^2
N1 = sub(W1, {Z=>a*(e2-1)+j*e2, Y=>a+j})
N1p = sub(N1,{e4=>e4^5,a=>a^5,e2=>e2^5})
factor(discriminant(N1p,j))
N1q = sub(N1p, {e4=>3*e2^2})
discriminant(N1q,j)
N1s = sub(N1p, {e2=>0})
discriminant(N1s,j)

----------p=7---------------

R = ZZ/7
S = R[a,e2,e4][Y,Z][j]
W1 = Z^5 + 3*Z^3*e4 + 3*Z*e4^2
N1 = sub(W1, {Z=>a*(e2-1)+j*e2, Y=>a+j})
N1p = sub(N1,{e4=>e4^7,a=>a^7,e2=>e2^7})
factor(discriminant(N1p,j))
sub(N1, {e2=>0})

----------p=11----------------


R = ZZ/11
S = R[a,e2,e4][Y,Z][j]
W1 = Z^9 + 3*Z^7*e4 + 10*Z^5*e4^2+2*Z^3*e4^3+5*Z*e4^4
N1 = sub(W1, {Z=>a*(e2-1)+j*e2, Y=>a+j})
N1p = sub(N1,{e4=>e4^7,a=>a^7,e2=>e2^7})
factor(discriminant(N1p,j))
sub(N1, {e2=>0})
