---This files contains the code needed to support the results claimed in Section 6 of the paper "ON THE ARITHMETIC AND GEOMETRY OF SPACES Lm+1,n" by Michel Matignon, Guillaume Pagot and Daniele Turchetti

---Numbering is consistent with that section of the paper and the code is written for the CAS Macaulay2 (version 1.15)

-----SECTION 6.1 (lambda=4)-----

---Program 6.1---

R = ZZ/3
S = R[a,s2,t2,t3,s4,t4,z][X]

Q1 = a*(X^4+s2*X^2-X+s4)
Q2 = X^4+t2*X^2-t3*X+t4
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 8 do (L = append(L, C_(X^(3*i - 1))))

I=ideal(L#0*z-1,L#1,L#2,L#3,L#4,L#5,L#6,L#7)
gens gb(I)

---Program 6.2---

R = ZZ/3
S = R[z,s2,t2,s4,t4,a,MonomialOrder=>Lex][X]

Q1 = a*(X^4+s2*X^2+s4)
Q2 = X^4+t2*X^2+t4
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 8 do (L = append(L, C_(X^(3*i - 1))))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#0*z-1)
G=gens gb(I)
G_0

---Program 6.3---

R = ZZ/3
S = R[z,t,s,a,MonomialOrder=>Lex][X]

Q1 = a*(X^4+s*X^2+a^8)
Q2 = X^4+t*X^2+1
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 8 do (L = append(L, C_(X^(3*i - 1))))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#0*z-1)
G=gens gb(I)
factor(G_(0,0))

---Program 6.4---

R = ZZ/3
S = R[z,t,a,MonomialOrder=>Lex][X]

Q1 = a*(X^4+(a^4-a^2-1)*X^2+a^8)
Q2 = X^4+t*X^2+1
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 8 do (L = append(L, C_(X^(3*i - 1))))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#0*z-1)
G=gens gb(I)
factor(G_(0,0))

--what happens if s=a^4-a^2-1=0:

J=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#0*z-1,a^4-a^2-1)
G=gens gb(J)

---Program 6.5---

R = ZZ/3
S = R[z,t,a,MonomialOrder=>Lex][X]

Q1 = a*(X^4+(a^4+a^2+a+1)*X^2+a^8)
Q2 = X^4+t*X^2+1
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 8 do (L = append(L, C_(X^(3*i - 1))))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#0*z-1)
G=gens gb(I)
factor(G_(0,0))

--what happens if s=a^4+a^2+a+1=0:

J=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#0*z-1,a^4+a^2+a+1)
G=gens gb(J)

-----SECTION 6.2 (lambda=5)-----

---Program 6.6---

R = ZZ/3
S = R[c,s2,t2,s4,t4,s5,t5,a][X]

Q1 = a*c*(X^5+s2*X^3+s4*X-s5)
Q2 = c*(X^5+t2*X^3+t4*X-t5)
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 10 do (L = append(L, C_(X^(3*i - 1))))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#8,L#9,L#0-1)
gens gb(I)

---Program 6.7---
clearAll

R = ZZ/3
S = R[b,c,t2,t3,t4,t5,s2,s4,s5,a, MonomialOrder => Eliminate 9][X];

Q1 = a*c*(X^5+s2*X^3-X^2+s4*X-s5)
Q2 = c*(X^5+t2*X^3-t3*X^2+t4*X-t5)
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 10 do (L = append(L, C_(X^(3*i - 1))//(a^2*c^6)));
L#0

I = ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#8,a^2*c^6*L#0-1,(a^3-a)*b-1);
gens gb(I)

---Program 6.8 (CASE 1)---

R = GF(9, Variable=>u)
a = u^2
a^2
S = R[c,t2,t3,t4,t5,s2,s4,s5][X]

Q1 = a*c*(X^5+s2*X^3-X^2+s4*X-s5)
Q2 = c*(X^5+t2*X^3-t3*X^2+t4*X-t5)
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 10 do (L = append(L, C_(X^(3*i - 1))//c^6))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#8,c^6*L#0-1)
G=gens gb(I)


---Program 6.9 (CASE 2)---

R =  GF(27, Variable=>u)
a=u^(-1)
a^3-a^2+1
S = R[c,t5,s5,t4,s4,t3,t2,s2][X]

Q1 = a*c*(X^5+s2*X^3-X^2+s4*X-s5)
Q2 = c*(X^5+t2*X^3-t3*X^2+t4*X-t5)
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 10 do (L = append(L, C_(X^(3*i - 1))//c^6))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#8,c^6*L#0-1)
G=gens gb(I)
G_(0,0)

--We then set t2=-(u^2+1)s2--
S = R[z,y,t3,t4,t5,s5,s4,s2][X]

Q1 = a*(X^5+s2*X^3-X^2+s4*X-s5)
Q2 = X^5-(u^2+1)*s2*X^3-t3*X^2+t4*X-t5
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 10 do (L = append(L, C_(X^(3*i - 1))))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#8,L#0*z-1)
G=gens gb(I)


---Program 6.10 (CASE 3)---

R = GF(27, Variable=>a)
a^3-a+1
S = R[z,y,t2,t3,t4,t5,s2,s4,s5][X]

Q1 = a*(X^5+s2*X^3-X^2+s4*X-s5)
Q2 = X^5+t2*X^3-t3*X^2+t4*X-t5
C = (Q1^3-Q1*Q2^2)^2

L = new List
for i from 1 to 10 do (L = append(L, C_(X^(3*i - 1))//c^6))

I=ideal(L#1,L#2,L#3,L#4,L#5,L#6,L#7,L#8,c^6*L#0-1)
G=gens gb(I)

