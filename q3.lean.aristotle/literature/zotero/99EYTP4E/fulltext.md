---
title: "Introduction to large truncated Toeplitz matrices"
authors:
  - "Albrecht B\u00f6ttcher"
  - "Bernd Silbermann"
date: "1999-00-00 1999"
publication: null
doi: "10.1007/978-1-4612-1426-7"
url: null
zotero:
  attachment_key: "NNPBIU32"
  parent_key: "99EYTP4E"
  item_id: 1954
  attachment_item_id: 2059
---

Springer Science+Business Media, LLC
Universitext
Editorial Board (North America):
S. Axler F.W. Gehring K.A. Ribet


 Universitext
Editors (North America): S. Axler, F.W. Gehring, and K.A. Ribet
AksoylKhamsi: Nonstandard Methods in Fixed Point Theory Andersson: Topics in Complex Analysis Aupetit: A Primer on Spectral Theory Berberian: Fundamentals of Real Analysis BoossIBleecker: Topology and Analysis Borkar: Probability Theory: An Advanced Course Bottcher/Silbermann: Introduction to Large Truncated Toeplitz Matrices CarlesonlGamelin: Complex Dynamics Cecil: Lie Sphere Geometry: With Applications to Submanifolds Chae: Lebesgue Integration (2nd ed.) Charlap: Bieberbach Groups and Rat Manifolds Chern: Complex Manifolds Without Potential Theory Cohn: A Classical Invitation to Algebraic Numbers and Cla~s Fields Curtis: Abstract Linear Algebra Curtis: Matrix Groups DiBenedetto: Degenerate Parabolic Equations Dimca: Singularities and Topology of Hypersurfaces Edwards: A Formal Background to Mathematics I alb Edwards: A Formal Background to Mathematics II alb Foulds: Graph Theory Applications Friedman: Algebraic Surfaces and Holomorphic Vector Bundles Fuhrmann: A Polynomial Approach to Linear Algebra Gardiner: A First Course in Group Theory GardingITambour: Algebra for Computer Science Goldblatt: Orthogonality and Spacetime Geometry GustafsonIRao: Numerical Range: The Field of Values of Linear Operators and Matrices Hahn: Quadratic Algebras, Clifford Algebras, and Arithmetic Witt Groups Holmgren: A First Course in Discrete Dynamical Systems HoweITan: Non-Abelian Harmonic Analysis: Applications of SL(2, R) Howes: Modern Analysis and Topology HumiIMiller: Second Course in Ordinary Differential Equations HurwitzIKritikos: Lectures on Number Theory Jennings: Modern Geometry with Applications JonesIMorrislPearson: Abstract Algebra and Famous Impossibilities KannanIKrueger: Advanced Analysis KellylMatthews: The Non-Euclidean Hyperbolic Plane Kostrikin: Introduction to Algebra LueckingIRubel: Complex Analysis: A Functional Analysis Approach MacLaneIMoerdijk: Sheaves in Geometry and Logic Marcus: Number Fields McCarthy: Introduction to Arithmetical Functions Meyer: Essential Mathematics for Applied Fields MineslRichmanIRuitenburg: A Course in Constructive Algebra Moise: Introductory Problems Course in Analysis and Topology Morris: Introduction to Game Theory Polster: A Geometrical Picture Book PorterlWoods: Extensions and Absolutes of Hausdorff Spaces RamsaylRichtmyer: Introduction to Hyperbolic Geometry Reisel: Elementary Theory of Metric Spaces Rickart: Natural Function Algebra~
(continued after index)


 Albrecht Bottcher Bernd Silbermann
Introduction to
Large lruncated
Toeplitz Matrices
With 62 Figures
, Springer


 Albrecht Bottcher Fakultăt fiir Mathematik Technische Universităt Chemnitz Chemnitz,09107 Germany
Editorial Board (North America):
S. Axler Mathematics Department San Francisco State University San Francisco, CA 94132 USA
K.A. Ribet Department of Mathematics University of California at Berkeley Berkeley, CA 94720-3840 USA
Bernd Silbermann Fakultăt fUr Mathematik Tcchnische Universităt Chemnitz Chemnitz, 09107 Germany
F.W. Gehring Mathematics Department East HalI University of Michigan Ann Arbor, MI 48109-11 09 USA
Mathematics Subject Classification (1991): 15-02,47B35
Library of Congress Cataloging-in-Publication Data Btitteher, Albreeht. Introduction to large truncated Toeplitz matrices / Albrecht Btittcher, Bernd Silbermann. p. cm. - (Universitext) Includes bibliographieal references and index. ISBN 978-1-4612-7139-0 ISBN 978-1-4612-1426-7 (eBook) DOI 10.1007/978-1-4612-1426-7 1. Toeplitz matrices. 1. Silbermann, Bernd, 1941II. Title. QA188.B67 1998 5 12.9'434-dc2 1 98-9923
Printed on aeid-free paper.
() 1999 Springer Scienee+Business Media New York OriginaJly published by Springer-Verlag New York, Ine. in 1999 Softcover reprint of the hardcover 1st edition 1999
Al! rights reserved. This work may not be translated or copied in whole or in part without the written permission of the publisher, Springer Science+Business Media, LLC except for brief excerpts in connection with reviews or scholarly analysis. Use in connection with any form of information storage and retrieval, electronic adaptation, computer software, or by similar or dissimilar methodology now known or hereafter developed is forbidden. The use of general descriptive names, trade names, trademarks, etc., in this publication, even if the former are not especially identified, is not to be taken as a sign that such names, as understood by the Trade Marks and Merchandise Marks Act, may accordingly be used freely byanyone.
Production managed by Alian Abrams; manufacturing supervised by Jeffrey Taub. Photocomposed copy provided from the authors' LATEX files.
9 8 765 4 321
ISBN 978-1-4612-7139-0


 Preface
Toeplitz matrices have been enjoying immense popularity for many decades. They are easily defined (as matrices constant along the parallels to the main diagonal), they emerge in a variety of problems of quite different natures, they cause interesting and difficult questions, and they usually lead to beautiful results. On the one hand, Toeplitz matrices are easy enough to serve as ideal illustrations of various abstract results and methods of linear algebra and functional analysis, and on the other hand, they are sufficiently nontrivial and therefore have the potential to create new concepts, techniques, insights, and, of course, to raise new questions. Figuratively speaking, the theory of Toeplitz matrices has grown to a grandiose city. Specialists know the parts of this city well and are about to reconstruct and expand it, but beginners and amateurs often have problems with finding their way in the labyrinth. This book is addressed to the latter group of people. It is intended as a guide to three main roads of this city, whose names are:
pseudospectra, singular values, eigenvalues,
and the book also contains glimpses at several side-streets. We consider large finite Toeplitz matrices as truncations of infinite Toeplitz matrices and hence, we study properties of an individual large finite Toeplitz matrix by embedding it into the sequence of the truncations (finite sections) of an infinite Toeplitz matrix.


 vi Preface
The three roads mentioned start at a place that bears the name
stability.
Given an infinite Toeplitz matrix A, let {An}~=l stand for the sequence of its n x n truncations. The central problem of the entire theory is as follows: if A induces an invertible operator, are the finite sections An invertible for all sufficiently large n, say for n ;::: no, and are the norms of the inverses, IIA;-lll, bounded from above by a finite constant independent ofn;::: no? If this is the case, the sequence {An} is said to be stable. Properties of infinite Toeplitz matrices (including invertibility criteria) are studied in Chapter 1 and the stability of sequences of truncated Toeplitz matrices is the topic of Chapter 2. Chapters 3,4, and 5 deal with pseudospectra, singular values, and eigenvalues of the truncated matrices An, respectively. The investigation of the pseudospectra of An is heavily based on the ability of computing the limit of II A;-lll as n goes to infinity. The computation of this limit is in turn a nice application of the theory of C*-algebras. The asymptotic distribution of the singular values of An is intimately tied in with asymptotic Moore-Penrose inversion of the matrices An. Finally, the main results on the asymptotic behavior of the eigenvalues of An are all derived from asymptotic formulas for the traces and determinants of Toeplitz-like matrices. Thus, we could also name our three main roads:
condition numbers, Moore-Penrose inversion, traces and determinants,
respectively. The matrices one encounters nowadays in applications are often not Toeplitz matrices but block Toeplitz matrices. Many results on Toeplitz matrices can be extended to block Toeplitz matrices, although this is usually a hard job. In accordance with the purpose of this text, we focus our attention on scalar Toeplitz matrices. However, in Chapter 6 we describe some of the phenomena caused by block Toeplitz matrices and cite several results, referring for proofs to the literature. In Chapter 7, we exhibit some results on Toeplitz operators on Banach spaces and acquaint the reader with certain techniques employed in this field. We remark that the Banach space theory of Toeplitz operators with piecewise continuous symbols is more beautiful than the corresponding Hilbert space theory! Moreover, we will exemplify in Chapter 7 that there are Hilbert space results which can be most easily understood by passing to Banach spaces. We suppose that knowledge of the basic facts of functional analysis in conjunction with some patience and persistence should suffice to enable a reading of the bulk of the text. Of course, the sights along the three roads mentioned will represent our taste, and some important topics are


 Preface vii
not treated at all. We would be happy if we could nevertheless convey to the reader an idea of what is known and of what is going on in the extensive and beautiful field of large Toeplitz matrices.
Acknowledgments. We wish to express our especially sincere gratitude to Sylvia Bottcher for the production of the 1l\TEX masters of the book and to Harald Heidler for making the majority of the computer pictures. We are greatly indebted to Torsten Ehrhardt and Steffen Roch for proof-reading the entire manuscript and for improving it by many useful remarks.
Chemnitz, December 1997
Albrecht Bottcher Bernd Silbermann


 Contents
Preface v
1 Infinite Matrices 1 1.1 Boundedness and Invertibility 1 1.2 Laurent Matrices . 3 1.3 Toeplitz Matrices . . . . . . 9 1.4 Hankel Matrices . . . . . . 13 1.5 Wiener-Hopf Factorization. 15 1.6 Continuous Symbols · .. 19 1.7 Locally Sectorial Symbols 20 1.8 Discontinuous Symbols . . 25
2 Finite Section Method and Stability 31 2.1 Approximation Methods 31 2.2 Continuous Symbols · . . . . . . 37 2.3 Asymptotic Inverses · . . . . . . 39 2.4 The Gohberg-Feldman Approach 44 2.5 Algebraization of Stability . 47 2.6 Local Principles. . . . . 52 2.7 Localization of Stability .. 56
3 Norms of Inverses and Pseudospectra 59 3.1 C*-Algebras . . . . . 59 3.2 Continuous Symbols · . . . . . . . . . 61


 x Contents
3.3 Piecewise Continuous Symbols 3.4 Norm of the Resolvent . . . . . 3.5 Limits of Pseudospectra . . . . 3.6 Pseudospectra of Infinite Toeplitz Matrices
4 Moore-Penrose Inverses and Singular Values 4.1 Singular Values of Matrices 4.2 The Lowest Singular Value 4.3 The Splitting Phenomenon 4.4 Upper Singular Values . . . 4.5 Moler's Phenomenon . . . . 4.6 Limiting Sets of Singular Values 4.7 The Moore-Penrose Inverse . . . 4.8 Asymptotic Moore-Penrose Inversion 4.9 Moore-Penrose Sequences . . . . . 4.10 Exact Moore-Penrose Sequences .. 4.11 Regularization and Kato Numbers
5 Determinants and Eigenvalues 5.1 The Strong Szego Limit Theorem 5.2 Ising Model and Onsager Formula 5.3 Second-Order Trace Formulas . 5.4 The First Szego Limit Theorem 5.5 Hermitian Toeplitz Matrices . . 5.6 The Avram-Parter Theorem .. 5.7 The Algebraic Approach to Trace Formulas 5.8 Toeplitz Band Matrices 5.9 Rational Symbols . 5.10 Continuous Symbols . . . . . 5.11 Fisher-Hartwig Determinants 5.12 Piecewise Continuous Symbols
6 Block Toeplitz Matrices 6.1 Infinite Matrices . . . . . . . . . . . . 6.2 Finite Section Method and Stability . 6.3 Norms of Inverses and Pseudospectra . 6.4 Distribution of Singular Values . . . 6.5 Asymptotic Moore-Penrose Inversion 6.6 Trace Formulas . 6.7 The Szego..Widom Limit Theorem 6.8 Rational Matrix Symbols . 6.9 Multilevel Toeplitz Matrices
7 Banach Space Phenomena 7.1 Boundedness .
64 69 70 80
83 83 85 86 94 95 98 100 108 108 111 116
121 121 127 132 136 138 143 147 153 163 165 170 179
185 185 191 196 197 198 201 203 205 208
221 221


 7.2 Fredholmness and Invertibility 7.3 Continuous Symbols . . . . . . 7.4 Piecewise Continuous Symbols 7.5 Loss of Symmetry .
References
Index
Symbol Index
Contents Xl
222 228 236 240
243
255
257


 1
Infinite Matrices
1.1 Boundedness and Invertibility
The purpose of this section is to fix some standard notations and to recall some terminology.
Bounded linear operators. Given a Banach space X, we denote by B(X) the collection of all bounded linear operators on X. The norm of an operator A E B(X) is defined in the usual way:
IIAII := sup IIAxll/llxll·
x~o
(1.1 )
We say that a sequence {An}~=l of operators An E B(X) converges uni
formly (or in the norm) to an operator A E B(X) if IIAn - All --> 0 as n --> 00, and the sequence {An}~l is said to converge strongly to A E B(X) if IIAnx - Axil --> 0 as n --> 00 for every x E X.
Infinite matrices. In what follows we are mainly concerned with the case where X is the Hilbert space l2(J) and J stands for the integers Z or the natural numbers N = {I, 2, 3, ... }. An orthonormal basis in l2(J) is constituted by the elements {ej} jE J where ej is the sequence (or the vector) whose jth entry is 1 and the remaining entries of which are zero. Thus, with every operator A E B(l2 (J)) we may associate the infinite matrix (ajk hkEJ given by
ajk = (Aek,ej). (1.2)
Thinking of l2 (J) as a space of infinite columns, we can describe the action


 2 1. Infinite Matrices
of A on l2(J) as multiplication by the infinite matrix (ajk)j,kEf we have
a-2,-2 a-2,-l a-2,O a-2,l X-2 Y-2 Ax= a-l,-2 a-l,-l a-I,O a-l,l X-l Y-I
aO,-2 aO,-l aOO aOl Xo Yo =y -al,-2 al,-l alO all Xl YI
and
with Yj = ~kEJ ajkXk in the cases J = Z and J = N, respectively. Every operator A E B(l2 (J)) can be represented by an infinite matrix as above, but not every infinite matrix defines a bounded operator on l2(J). We say that an infinite matrix (ajk)j,kEJ generates a bounded operator on l2(J) (or simply that the infinite matrix is a bounded operator on l2(J)) if there exists an A E B(l2(J)) such that (1.2) is valid for all j, k E J, Equivalently, the infinite matrix (ajk)j,kEJ generates a bounded operator on l2 (J) if and only if there exists a constant M < 00 such that for every X E l2(J) the following hold:
(i) the series Yj := ~kEJ ajkXk converge for all j E J;
(ii) y:= {Yj}jEJ belongs to l2(J);
(iii) lIyll :::; MllxlI;
here, of course, 11·11 is nothing but the norm in l2(J). The smallest constant
M for which this is true equals the norm IIAII of the operator A E B(l2(J)) induced by the given infinite matrix.
Banach algebras. A (complex) Banach space A with an associative and distributive multiplication is called a Banach algebra if Ilabll :::; Ilalillbll for all a, bE A. If a Banach algebra has a unit element (which is also frequently called the identity), then this element is usually denoted bye, 1, or I. We always require that Ilell = 11111 = 11111 = 1.
Invertibility and spectrulll. Let A be a Banach algebra with the unit element e. An element a E A is said to be invertible (in A) if there is an element b E A such that ab = ba = e. The element b is uniquely determined whenever it exists; in that case it is denoted by a-I and is called the inverse of a. The spectrum of an element a E A is defined as the set
spa := sPAa := {,,\ E C : a -,,\e is not invertible in A}.


 1.2 Laurent Matrices 3
It is well known that the spectrum of an element of a Banach algebra with identity is always a nonempty compact subset of the complex plane C which is contained in the disk {A E C : 1,\1 S; Ilall}· If X is a Banach space, then B(X) is a Banach algebra with obvious algebraic operations and the norm (1.1). The unit of B(X) is the identity operator I. An operator A E B(X) is called invertible if it is invertible as an element of B(X), and the spectrum of A is simply the set spl3(x)A.
1.2 Laurent Matrices
Suppose we are given a sequence {an}~=-oo of complex numbers and A is the infinite matrix
ao a-I a-2 a-3 a-4 al ao a-I a-2 a-3 A= a2 al ao a-I a-2 (1.3) a3 a2 al ao a-I a4 a3 a2 al ao
Such matrices, that is, doubly-infinite matrices which are constant along the diagonals, are called Laurent matrices. When does A generate a bounded operator on l2(Z)? The answer is given by the following well-known result.
Theorem 1.1. The Laurent matrix (1.3) generates a bounded operator on l2(Z) if and only if there is a function a E Loo(T) such that {an}~=_oo is the sequence of the Fourier coefficients of a:
(n E Z).
Here and in what follows, T stands for the complex unit circle {z E
C : Izl = I}. The function a E LOO(T) (or better: the equivalence class of Loo(T) containing a) whose existence is ensured by this theorem is determined uniquely. We therefore denote the matrix (1.3) as well as the bounded operator generated by this matrix on l2(Z) by L(a). The function a is in this context usually referred to as the symbol of the matrix or the operator L(a).
Multiplication operators. Let LP := LP(T) (1 S; p S; 00) be the usual
Lebesgue spaces on T and denote by II . II p the norm in LP. For a E L00 , the multiplication operator


 4 1. Infinite Matrices
is obviously bounded. Clearly, IIM(a)11 :::; lIall oo . It is not difficult to show
that actually IIM(a)1I = lIall oo and that M(a) is not bounded if a does not belong to Loo. Denote by
the operator which sends a function to the sequence of its Fourier coefficients. The operator <l> is bijective and, by Parseval's equality,
The basic properties of Laurent matrices follow from the fact that they are the matrix representations of multiplication operators on L2 with respect to the orthonormal basis
{ 1 ino}
J27re nEZ·
In other words, we have
L(a) = <l>M(a)<l>-I. (1.4)
For example, this equality at once implies the "if" portion of Theorem 1.1; it is the key to the proof of the "only if" part as well. Also notice that (1.4) shows that
and
L(a)L(b) = L(ab) for all a, bE L oo
IIL(a)11 = Iiall oo for all a E L oo .
(1.5)
(1.6)
Essential range. The space L oo is a Banach algebra under pointwise operations and the norm 11·1100. For a E Loo , we denote by R(a) the spectrum of a as an element of L OO • Equivalently, we may define R(a) as the spectrum of the multiplication operator M (a) on L 2 . Finally, it is not hard to see that
R(a) = {A E C: I{t E T: la(t) - AI < e}1 > 0 V c > o},
where lEI stands for the Lebesgue measure of E. The (nonempty and compact) set R(a) is called the essential range of a. Notice that alteration of a on a set of measure zero does not change R(a).
Theorem 1.2. If a E Loo , then sp L(a) = R(a). If 0 rt. R(a), then the inve-rse of L(a) is L(a- 1).
This follows easily from (1.4) and (1.5). Under some additional hypotheses, Theorem 1.2 was first proved by Otto Toeplitz [1691.
We now discuss a few concrete symbol classes.


 1.2 Laurent Matrices 5
Example 1.3: band matrices. If L(a) is a band matrix, i.e. if an = 0 for Inl > N, then the symbol a is a trigonometric polynomial:
N
a(t) = L antn (t = eiO E T).
n=-N
In particular, the symbol of the matrix
1
oooo
2 1
ooo
1 2 1
oo
o
1 2
1
o
oo
1 2 1
ooo
1 2
(1. 7)
is
It follows from Theorem 1.2 that the spectrum of the operator given on [2(Z) by (1.7) is the line segment [0,4]. Some more interesting symbols of Toeplitz band matrices are in Figure 1.•
20 1.5 15 Fig. 1a Fig. 1b
10 0.5
5 0 0
-5 -0.5
-10 -1
-15 -1.5
-20 -10 0 10 20 -2 -1 0 2
In Figures 1a and 1b we plotted R(a) for two trigonometric polynomials a.
Example 1.4: rational symbols. The restriction of a rational function a to T belongs to L OO if and only if the function a has no poles on T. Such symbols define Laurent matrices whose entries decay as a geometric


 6 1. Infinite Matrices
sequence. For example, the symbol of the matrix
[3 1 a a 2 a 3 a 4
[32 [3 1 a a 2 a 3
[3 [3 [3 1 a a (Ial < 1, 1[31 < 1)
[34 [33 [32 [3 1 a [35 [34 [33 [32 [3 1
is (see Figure 2)
2 Fig.2a 5 Fig. 2b -~
+
o
-I
o2
o
-5
.
+
o 5 10
Figures 2a and 2b show R(a) for two symbols as in Example 1.4. The corresponding points a and [3 are marked by * and +, respectively.
Example 1.5: symbols in the Wiener algebra. If LnEZ lanl < 00, then the matrix L(a) has the symbol
a(t) = L antn (t = eiO E T).
nEZ
The set of all such functions is denoted by W := W(T) and is called the Wiener algebra. It is a Banach algebra with pointwise algebraic operations and the norm
Iiallw:= L lanl·
nEZ
Clearly, W is contained in the Banach algebra C := C(T) of all (complexvalued) continuous functions on T with the maximum norm. Wiener's theorem says that if a E Wand a has no zeros on T, then a-I = l/a E W.


 1.2 Laurent Matrices 7
Thus, by Theorem 1.2, the inverse of an invertible Laurent operator with a symbol in the Wiener algebra is again a Laurent operator with a symbol in the Wiener algebra.•
Example 1.6: continuous symbols. The essential range of a function a E C is its image a(T) and hence, sp L(a) = a(T). There are many functions in C\ W, but these are sometimes difficult to identify in terms of their Fourier coefficients. To get an idea of the problem, let us look at a special class of functions. Suppose {bn}~=2 is a sequence of positive numbers converging monotoneously to zero and consider the series
I>n sin nO = f: ~: (einO - e-inO )
n=2 n=2
(e iO E T). (1.8)
The following result is well known (see, e.g., [68, Section 7.2.2]):
(i) the series (1.8) is the Fourier series of a function in C if and only if
bn = o(l/n) as n ---+ 00;
(ii) the series (1.8) is the Fourier series of a function in L')Q if and only if
bn = O(l/n) as n ----> 00.
In particular, the symbol of the Laurent matrix induced by {an}nEZ with
1
an = ---:--.,........,.
nlog Inl (Inl ::::: 2)
belongs to C\ W, while the Laurent matrix defined by {an}nEZ with
a-I = ao = al = 0, an = log Inl (Inl::::: 2)
n
does not generate a bounded operator on l2(Z) .•
Example 1.7: piecewise continuous symbols. A function a E L oo is
said to be piecewise continuous if for every t = eiO E T the one-sided limits
a(t + 0):= lim a(ei(o+c)),
10--->0+0
a(t - 0):= lim a(ei(O-c))
10--->0+0
exist. We always think of the unit circle T as being oriented counterclockwise, which also accounts for the notations a(t - 0) and a(t + 0). The set of all piecewise continuous functions is denoted by PC := PC(T). It is well known that PC is a closed subalgebra of Loo . Functions in PC have at most countably many jumps, i.e., if a E PC, then the set
Aa := {t E T: a(t - 0) # a(t + On


 8 1. Infinite Matrices
is at most countable. Moreover, for each 8 > 0 the set
{t E T: la(t +0) - a(t -0)1> 8}
is finite. Given a E PC, we always assume that a is continuous on T\Aa . Thus,
R(a) = U {a(t)} U U {a(t - 0), a(t + On· (1.9)
tET\1\o tE1\o
Theorem 1.2 tells us that (1.9) is the spectrum of L(a).
5 Fig. 3a
o
-5
-5 o 5
5 Fig.3b
o
-5
-5 o 5
Figure 3a shows the set R('IjJ-y) for, = 0.8 and, = 0.8 + 0.3i, in
Figure 3b we plotted R('IjJ-y) for, = -0.8, , = -0.8 + O.li, and
, = -0.8 + i. The points 'IjJ-y(1 + 0) and 'IjJ-y(1 - 0) are marked by * and 0, respectively.
5 Fig.4a 5 Fig.4b
o
-5
-5 o 5
o
-5
-5 o 5
In Figure 4a we see the set R('IjJ-y) for, = -1.5 + O.li and in Figure 4b we have R('IjJ-y) for, = 3.25 + 0.3i. The points 'IjJ-y(1 + 0) and
'IjJ-y(1 - 0) are again marked by * and 0, respectively. Figure 4b convincingly indicates that R('IjJ-y) is a piece of a logarithmic spiral. Thus, we encounter once more the phenomenon that logarithmic spirals are everywhere (see [42]' [32]).


 1.3 Toeplitz Matrices 9
To have a concrete example, pick r E C\Z and put
W(eilJ ) = _._7r_ei1r'Ye-i'YlJ, () E [0, 27r).
'Y sm 7r'Y (1.10)
A moment's thought reveals that this is a function in PC with a single
jump at eilJ = 1:
7r .
W (1 + 0) = _._ _ et1r'Y,
'Y sm 7rr
7r .
W(1 - 0) = -._ e - t1r'Y.
'Y sm 7rr (1.11)
A straightforward computation gives
1
(W'Y)n = n + r (n E Z),
i.e.,
L(W'Y) = C-~ + r) ~k=-oo
is a so-called Cauchy-Laurent matrix. By Theorems 1.1 and 1.2, the Laurent operator L(W'Y) is bounded and
IIL(W'Y)II = Isi:7rrl e1r11ffi 'Yl,
spL(W ) = {.-;!!..-ei1r'Ye-i'YlJ: () E [0, 27r1}.
'Y sm 7rr
Figures 3 and 4 show plots of the essential range of W'Y .•
Example 1.8: a glance at the abyss of Loo. Every compact set M c C is the spectrum of some Laurent operator. Indeed, let {Zj}jEN be a countable dense subset of M, let {Ej } jEN be a sequence of pairwise disjoint arcs Ej C T whose union is all of T, and define a E LOO as
a = L ZjXEj' jEN
where XE is the characteristic function of E. Then spL(a) = R(a) = M .•
1.3 Toeplitz Matrices
The Toeplitz matrix defined by a sequence {an}~=_oo of complex numbers is the infinite matrix
C'
a-I a-2 )
A = al ao a-I ... (1.12)
a2 al ao


 10 1. Infinite Matrices
We henceforth abbreviate l2 (N) to l2.
Theorem 1.9. The Toeplitz matrix (1.12) generates a bounded operator on l2 if and only if there is a function a E Uxo whose sequence of Fourier coefficients is the sequence {an}nEZ,
This theorem was established by Toeplitz [169] in 1911. Notice that Toeplitz' paper actually deals with Laurent matrices and that the main result of his paper is Theorem 1.2. However, Theorem 1.9 is proved in a footnote of [169] and it is this theorem which led to naming the matrices (1.12) after Toeplitz. Independently, Theorem 1.9 was also found by Brown and Halmos [43]. Full proofs of Theorem 1.9 are in [39, Theorem 2.7]' [43], [95, Problem 194]' for example. In what follows we only need the "if portion" of Theorem 1.9, which can be easily proved. Indeed, identify l2 as a subspace of l2(Z) in the natural manner and denote by P the orthogonal projection of l2(Z) onto l2. Then the operator A given by the matrix (1.12) can be identified with PL(a)P. This and the sufficiency portion of Theorem 1.1 show that A generates a bounded operator on l2 whenever a E Loa. From (1.6) we also infer that
IIAII = IIPL(a)PII :::; IIL(a)11 = Iiall oo · (1.13)
The function a E Loa given by Theorem 1.9 is called the symbol of the Toeplitz matrix (1.12) and of the operator induced by this matrix on l2. Throughout the following we denote (1.12) by T(a).
Norm of a Toeplitz operator. It is well known that for every a E Loo the equality
IIT(a)11 = Iialloa (1.14)
holds. The estimate IIT(a)1I :::; Iiall oo is contained in (1.13). To prove the reverse inequality, denote by Sn (n = 1,2,3, ... ) the projection on l2(Z) given by
if k < -n, if k 2: -no
Obviously, Sn ----+ I strongly on l2(Z). It follows that SnL(a)Sn converges strongly to L(a), and because evidently IISnL(a)Snll = IIT(a)ll, we deduce from the Banach-Steinhaus theorem (see Theorem 2.1 below) that
IIL(a)11 :::; liminf IISnL(a)Snll = IIT(a)ll·
n->oo
Now (1.6) implies that IIT(a)11 2: Iiall oo .
Spectrum of a Toeplitz operator. The spectra of Laurent operators are completely described by Theorem 1.2. The determination of the spectra of Toeplitz operators is a much more difficult problem. In the case where


 1.3 Toeplitz Matrices 11
a E C, we will identify spT(a) in Section 1.6. Some more results on the spectra of Toeplitz operators will be discussed in Section 1.8. The rest of this section is devoted to Coburn's lemma, which divides the problem of deciding whether a Toeplitz operator T(a) is invertible into finding out whether T(a) is Fredholm and into computing the index of T(a).
Fredholmness and index. Let X be a Banach space and A E B(X). The kernel and the image (= range) of A are defined by
Ker A:= {x EX: Ax = O}, ImA:= {Ax: x EX}.
The operator A is said to be Fredholm if 1m A is a closed subspace of X and the two numbers
a(A) := dimKer A, ,B(A) := dim (X/1m A)
are finite. The space X/1m A is also frequently referred to as the cokernel of A and denoted by Coker A. If A is Fredholm, the index of A is defined as the integer
IndA := a(A) - ,B(A).
Calkin algebra and essential spectrum. Let K(X) denote the set of all compact operators on a Banach space X. It is well known that K(X) is a closed two-sided ideal of the Banach algebra B(X). One can show that an operator A E B(X) is Fredholm if and only if the coset A + K(X) is invertible in the quotient algebra B(X)/K(X) (see, e.g., [87, Chapter 4, Theorem 7.1] or [59, Theorem 5.17]). The algebra B(X)/K(X) is also referred to as the Calkin algebra of X. The essential spectrum sPess A of A E B(X) is the spectrum of A + K(X) in B(X)/K(X), that is,
sPess A := {>. E C : A - >..I is not Fredholm on X}.
Clearly, sPess A C spA.
Hardy spaces. In Section 1.2 we saw that the basic properties of Laurent matrices result from the fact that they are canonical matrix representations of multiplication operators on £2. To proceed in an analogous way in the context of Toeplitz operators, we need the Hardy spaces H 2 := H 2 (T) and H:' := H:' (T). By definition,
H 2 := {f E £2 : In = 0 for n < O}, H::= {f E £2: In = 0 for n ~ O},
where {In}nEZ is the sequence of the Fourier coefficients of I. The spaces H 2 and H:' are closed subspaces of £2, and it is clear that £2 decomposes into the orthogonal sum


 12 1. Infinite Matrices
Let P stand for the orthogonal projection of L2 onto H2. The functions
{
I ino}OO
V21i e
n=O
form an orthonormal basis in H 2 , and it can be readily verified that if
a E L oo , then the matrix representation of the operator
(1.15)
is just the Toeplitz matrix T(a). Notice that the operator (1.15) is the
compression PM(a)P of the multiplication operator M(a) to H 2.
A crucial property of functions in H 2 is revealed by the F. and M. Riesz
theorem: a function in H 2 vanishes either almost everywhere or almost nowhere on T (see, e.g., [59, Theorem 6.13]).
Theorem 1.10 (Coburn's Lemma). Let a E Loo and suppose a does not vanish identically. Then T(a) has a trivial kernel on l2 or its image is dense in l2. In particular, T( a) is invertible if and only if T( a) is Fredholm of index zero:
spT(a) = sPes,; T(a) U {A E C \ sPess T(a) : Ind (T(a) - AI) -:J O}. (1.16)
Proof. The adjoint operator of T( a) is T(a) where a( t) := a(t) for t E T and the bar denotes complex conjugation. Assume that T(a) has a nontrivial kernel and that the image of T(a) is not dense. The latter assumption implies that T(a) has a nontrivial kernel. Hence, there are nonzero functions 1+ E H 2 and g+ E H 2 such that a1+ =: f _ E H: and ag+ =: 9_ E H: (recall (1.15)). By the Riesz brothers' theorem, 1+ -:J 0 and 9+ -:J 0 almost everywhere (a.e.) on T. We have
9-1+ = a?i+1+ = a1+9+ = f-9+ =: cp.
Obviously, cp E L 1 . Moreover, CPn = (9-1+)n = 0 for n :::; 0 and CPn = (J-9+)n = 0 for n ~ O. Consequently, cP = O. Since 1+ -:J 0 a.e. on T, we conclude that 9_ = 0 a.e. on T, and since 9_ = a9+ and 9+ -:J 0 a.e. on T, it follows that a = 0 a.e. on T. This contradicts the hypothesis of the theorem and shows that T(a) has a trivial kernel or a dense range. Now suppose T(a) is Fredholm of index zero. Then KerT(a) = {O} or 1m T(a) = l2 by what was already proved. If T(a) were not invertible, we had a(T(a)) > 0 and (J(T(a)) = 0 or a(T(a)) = 0 and (J(T(a)) > O. In
either case it would follow that Ind T(a) -:J o. Thus, T(a) must be invertible. Finally, (1.16) results from the equality T(a) -).[ = T(a - A) .•
Theorem 1.10 was established by Coburn [49] and independently (and in a more general setting) also by Simonenko [161]. For continuous symbols, the theorem is already in Gohberg's paper [78].


 1.4 Hankel Matrices 13
1.4 Hankel Matrices
With each sequence {an}nEZ of complex numbers we associate two Hankel matrices
:::), A = (:=~ :=: a-3 :::).
... a-3 ... . ..
... ... . ..
(1.17)
The problem of describing the sequences {an}nEZ for which A or A generate a bounded operator on [2 is more delicate than in the Laurent and Toeplitz cases. Its solution is given by the following theorem.
Theorem 1.11 (Nehari). The matrix A (resp., A) generates a bounded
operator on l2 if and only if there is a function b E Loo such that bn = an (resp., b_n = a_ n) for all n 2: 1.
A proof of this result is in almost every text on Hankel and Toeplitz operators. We here confine ourselves to a few remarks. Let a E L00 and let {an }nEZ be the sequence of the Fourier coefficients of a. We then denote by H (a) the matrix A of (1.17) and by H (ii) the matrix A of (1.17). Thus, for each a E Loo we define two Hankel matrices H(a) and H(ii). However, note that if we assign a new function ii E Loo to a by the formula
ii(t) := a(l/t) (t E T), (1.18)
then H(ii) is nothing but H(c) with c = ii. If a E Loo, then the boundedness of H(a) and H(ii) is immediate from Theorem 1.1, because H(a) is the left lower quarter and H(ii) is the right upper quarter of L(a). To be more precise, define P, Q, J on l2(Z) as follows:
(PX)k := { ~k
(JX)k := X-k-l.
for k 2: 0,
for k < 0, (QX)k := { ~k for
for
k < 0, k 2: 0,
An easy computation shows that
H(a) = PL(a)QJIIm P and l!(ii) = JQL(a)PIIm P,
which proves that IIH(a)1I and IIH(ii)11 do not exceed IIL(a)1I = Iialloo .
Caution. Let A be the left matrix of (1.17) and suppose A generates a bounded operator on [2. Then, by Theorem 1.11, there is abE Loo such that A = H(b). However, this does not imply that there exists acE Loo
such that Cn = °for n S °and Cn = an for n 2: 1, i.e., the function C given


 14 1. Infinite Matrices
formally by
00
c(t) = L antn (t E T)
n=l
need not belong to L 00. To see this, consider the function
b(eiO ) = -iB, BE [0, 27l").
Clearly, b E PC c LOO and
(1.19)
H(b)~ U
but the function
21
31"
31" ... )
... ,
is not bounded.
Norm of a Hankel operator. Given a E Loo, there are infinitely many different functions bE Loo such that H(a) = H(b). One can show that
IIH(a)11 = inf{llblloo : H(b) = H(a)}. (1.20)
The role played by Hankel matrices in Toeplitz theory is uncovered by the following simple but important result.
Proposition 1.12. If a, bE Loo, then
T(ab) = T(a)T(b) + H(a)H(b).
Proof. With P, Q, J as above, this is nothing but the obvious identity
PabP = PaPbP + PaQbP = PaPPbP + PaQJJQbP..
Thus, unlike (1.5), the product of two Toeplitz matrices is in general not a Toeplitz matrix.
Notes. Theorem 1.11 and the equality (1.20) are due to Nehari [126]. Full proofs are in [39, Theorem 2.11], [127, Lecture VIII], [129, Chapter 3], [135, Chapter 1]' and [147, Chapter 9]. Results like Proposition 1.12 have been used for more than fifty years; in the form cited here, Proposition 1.12 appeared in Widom's paper [185] for the first time.


 1.5 Wiener-Hopf Factorization 15
1.5 Wiener-Hopf Factorization
Triangular Toeplitz matrices. Let
The sets HOO and Hoo are obviously closed subalgebras of the Banach algebra LOO. Clearly, Hoo n Hoo = C, where C here refers to the constant
functions. While H 2 + H~ = L2 (recall Section 1.3), the sum HOO + Hoo
does not coincide with Loo ; for instance, function (1.19) can be shown to
be not in H oo + Hoo. If a E Hoo, then H (a) = 0 and T(a) is lower triangular. Analogously, if a E Hoo, then H(a) = 0 and T(a) is upper triangular. These observations and Proposition 1.12 imply the following fact.
Proposition 1.13. If a E Hoo, b E Loo, c E H oo , then
T(abc) = T(a)T(b)T(c) .•
This proposition is the origin of the so-called Wiener-Hopf factorization.
Given a E Loo , one looks for functions a_ E Hoo and a+ E HOC such that a = a_a+. Provided we have found a_ and a+, we can factorize T(a) = T(a_)T(a+) by virtue of Proposition 1.13. If, in addition, a__ is invertible in Hoo and a+ is invertible in Hoo, then, again due to Proposition 1.13,
T(a=l)T(a_) = T(a=la_) = I = T(a_a=l) = T(a_)T(a=l),
T(a:t1)T(a+) = T(a:t1a+) = I = T(a+a:t 1) = T(a+)T(a:t 1),
which shows that T(a) is invertible and that
Note that if a E Hoo is invertible in Loo, then a need not necessarily be
invertible in H oo (example: a(ei9 ) = ei9 ). Our next purpose is to construct a Wiener-Hopf factorization for functions in the Wiener algebra W (recall Example 1.5).
The group of invertible elements. Let A be a Banach algebra with identity element e. We denote by GA the collection of all invertible elements of A. The set GA is a multiplicative group and an open subset of A. Let GoA stand for the connected component of GA which contains the identity. If A is commutative, then
a E GoA {=} a = exp(b) with some bE A
(see, e.g., [59, Corollary 2.15]).
(1.21 )


 16 1. Infinite Matrices
Winding number. The group GC := GC(T) consists precisely of the functions in C which have no zeros on T. For a E GC, we denote by wind(a,O) the winding number of a with respect to the origin: every function a E GC may be written in the form a = laleic where c : T\ {I} -> R is continuous, and wind(a, 0) is defined as the integer
-1 (c(1 - 0) - c(1 + 0) ) .
21r (1.22)
Notice that c is unique up to an additive constant of the form 2k1r (k E Z) and that (1.22) does not depend on the particular choice of c. If a E C(T) and ,\ E C\a(T), we define the winding number wind(a,'\) of a with respect to ,\ by wind(a,'\) = wind(a - '\,0) (see Figure 5).
5,------,----,------,----,-------,-----,
4 Fig. 5
3
o
24
2
0
-1
-2
-3
-4 ->
-5 -4 -2 0
The "dolphin" curve in Figure 5 divides the plane into four regions. Figure 5 shows the winding number of the curve with respect to the points in these regions.
For nEZ, we define Xn by Xn(t) = t n (t E T). Equivalently, Xn(eiO ) = einO . By the definition of the winding number, wind(Xn, 0) = n. It is easily seen that if a, bE GC, then
wind(ab, 0) = wind(a, O) + wind(b,O).
Further, it is well known that
GoC = {a E GC: wind(a,0) = OJ. (1.23)


 1.5 Wiener-Hopf Factorization 17
By Wiener's theorem, we have GW = W n GC. One can show that the analogue of (1.23) is also true in the Wiener algebra:
GoW = {a E GW: wind(a,O) = O}. (1.24)
Theorem 1.14 (Wiener-Hopf factorization for Wiener functions). Let a E W n GC and let wind(a, 0) = K. Then
(1.25)
where a_ E W n GHoo and a+ E W n GHoo.
The following proof shows how the factors a± can be found.
Proof. Since wind(ax_x,O) = 0, we deduce from (1.21) and (1.24) that ax-x = eb with b E W. Thus,
b(t) = L bntn (t E T) and
nEZ
Define b+ E W n H oo and b- E W n Hoo by
L Ibnl < 00.
nEZ
00
b+(t) = L bntn , n=O
-1
b_(t) = L bntn (t E T).
n=-()()
We have b = b- + b+ and hence (1.25) holds with a_ := eb- and a+ := eb+.
Obviously, a+ 1 = e- b+ E W n HOO and a=l = e-b- E W n Hoo . •
Analytic Wiener functions. Put W+ := WnH oo and W_ := WnHoo. The preceding proof worked for functions in W because W = W _ + W + (and it does not work for functions in Loo for several reasons, one being
that LOO 1= Hoo + HOO).
Let D := {z E C : Izi < 1} be the open unit disk. If a+ E W+, then a+ can be extended to an analytic function in D by the formula
00
a+(z) := L anzn (z ED), n=O
where {an}~=o is the sequence of the Fourier coefficients of a. Analogously, a function a_ E W _ admits analytic continuation to (C U {oo} ) \ (D U T) via 00
a_(z) := L a_nz-n (z lit D U T). n=O
One can show that if a± E W ±, then
a+ E W n G H oo <=? a+ E GW+ <=? a+ (z) 1= ° \IzED U T,
a_EWnGHoo <=? a_EGW_ <=? a_(z) 1=0 \lZE(CU{oo})\D.


 18 1. Infinite Matrices
Theorem 1.15 (M.G. Krein). Suppose a E W. The operator T(a) is Fredholm on 12 if and only if a has no zeros on T. In that case
Ind T(a) = -wind(a, 0).
In particular, T(a) is invertible if and only if a(t) -=I- °for all t E T and
wind( a, 0) = 0. In the latter case, the inverse is
where a = a_a+ is any factorization as in Theorem 1.14.
Proof. Assume a has no zeros on T, put x := wind(a,O), and factorize a as in (1.25). Then T(a) = T(a-)T(Xx)T(a+) due to Proposition 1.13, and the operators T(a±) are invertible by the remark after Proposition 1.13. Looking at the matrix of T(Xx) it is readily seen that T(Xx) is Fredholm and that
a(T(xx)) = max{-x,O}, ,8(T(Xx)) = max{O,x}.
Consequently, Ind T(Xx) = -x. This implies that T(a) is Fredholm and that
Ind T(a) = Ind T(a_) + Ind T(Xx) + Ind T(a+) = °+ (-x) + 0 = -x.
Now assume the curve a(T) passes through the origin but T(a) is Fredholm. Let x := Ind T(a). On slightly perturbing a, we can produce functions b, c E W without zeros on T such that Iia - bll oo and Iia - cll oo are as small as desired and Iwind(b,O) - wind(c, 0)1 = 1. As the property of being Fredholm and the index are stable under small perturbations, it follows that T(b) and T(c) are Fredholm and that IndT(b) = IndT(c) = x. However, from what was already proved we know that
IIndT(b) - IndT(c)1 = Iwind(b,O) - wind(c, 0)1 = 1.
This contradiction shows that T(a) cannot be Fredholm. The assertions concerning the invertibility and the inverse ofT(a) follow from Theorem 1.10 and the discussion after Proposition 1.13.•
Notes. The books [87] and [59] contain very readable expositions of the properties of GA and of Fredholm operators we used in this section. What we call Wiener-Hopf factorization is a method which was developed by Gakhov [75], [76] (but see also Plemelj's paper [134]). Mark Krein [110] was the first to understand the Banach algebraic background of WienerHopf factorization and to present the method in a crystal-clear manner. The results of this section are all due to him.


 1.6 Continuous Symbols 19
1.6 Continuous Symbols
Since Fredholmness is equivalent to invertibility modulo compact operators, Proposition 1.12 motivates the search for compactness criteria for Hankel operators. The following theorem provides such a criterion.
Theorem 1.16 (Hartman). The matrix A of (1.17) generates a compact operator on l2 if and only if there is a function bEe such that bn = an for all n 2: 1. Equivalently, if a E L'~o, then H (a) is compact on l2 if and only if
a E e + Hoo := {c + 9 : c E e, 9 E Hoo}.
This theorem is proved in many standard texts on Hankel and Toeplitz operators. In what follows, we merely need the sufficiency part of the the
orem, which can be easily verified. Indeed, let c E e and g E Hoo. Then
H(c + g) = H(c), and we are left with showing that H(c) is compact. Let {'fin}~=l be any sequence of trigonometric polynomials converging uniformly to c on T; for instance, let 'fin be the nth Fejer-Cesaro mean of c. We then have
IIH(c) - H('fin)ll = IIH(c - 'fin)11 ::; lie - 'fin 1100 = 0(1),
and as the operators H ('fin) have finite rank, it follows that H (e) is compact. We are now in a position to describe the spectra of Toeplitz operators
with continuous symbols. If a E e, then aCt) traces out a continuous closed oriented curve aCT) as t traverses T in the counterclockwise direction. As in Section 1.5, given ,\ E C\a(T), we let wind(a,'\) stand for the winding number of the curve aCT) about '\, that is, wind(a,'\) := wind(a -'\,0).
Theorem 1.17 (Gohberg). Let a E e. The operator T(a) is Fredholm on the space l2 if and only if a has no zeros on T, in which case
Ind T(a) = -wind(a, 0).
Equivalently,
sPess T(a)
spT(a)
aCT),
aCT) U {,\ E C\a(T): wind(a,'\) 1= o}.
(1.26)
(1.27)
Proof Suppose first that a E Ge. By Proposition 1.12,
T(a-I)T(a) = I - H(a-I)H(a),
T(a)T(a- l ) = I - H(a)H(a- I),


 20 1. Infinite Matrices
and since all occurring Hankel operators are compact due to (the sufficiency portion of) Theorem 1.16, the oper3tor T(a- 1 ) is an inverse of T(a) modulo compact operators. This shows that T(a) is Fredholm. Let wind(a,O) = x. Then a is homotopic to the function Xx defined by Xx(t) = t X (t E T) within GG. Therefore
IndT(a) = IndT(xx).
In the proof of Theorem 1.15 we observed that Ind T(Xx) = - x. The index perturbation argument of the proof of Theorem 1.15 yields that necessarily a E GG if T(a) is Fredholm. Finally, since T(a) - >..I = T(a - >.), we arrive at (1.26) and (1.27) .•
300 300 Fig.6a 200 200
100 100
00
-100 -100
-200 -200
-300 -300
-400 -200 0 200 400 -400 -200 0
Fig.6b
200 400
For a special symbol a, we see sPess T(a) in Figure 6a, while spT(a) is indicated in Figure 6b.
Notes. Theorem 1.16 was established by Hartman [971. Full proofs are in [39, Theorem 2.54], [127, Lecture VIII], [129, Chapter 3], [135, Chapter 1]' or [147, Chapter 9]. Theorem 1.17 has a long history. That T( a) is Fredholm and has the index -wind(a, 0) whenever a E GG is more or less explicit in the works by F. Noether, S.G. Mikhlin, N.I. Muskhelishvili, F.D. Gakhov, V.V. Ivanov, M.G. Krein, A.P. Calderon, F. Spitzer, H. Widom, A. Devinatz, G. Fichera, and certainly others. In the form cited here, the theorem appeared in Gohberg's papers [77], [781. Figure 6 illustrates Theorem 1.17.
1.7 Locally Sectorial Symbols
We now turn to Toeplitz operators with discontinuous symbols. The following result provides a useful upper estimate of the spectrum.


 1. 7 Locally Sectorial Symbols 21
Theorem 1.18 (Brown-Halmos). If a E LOO then
spT(a) c convR(a),
where cony R(a) stands for the convex hull of the essential range R(a) of the function a.
Proof. Let A E C\convR(a) and put b = a - A. Then 0 (j. convR(b). Hence, there is a lET such that I conv R( b) = conv R(Tb) is completely contained in the right open half-plane. This implies that we can find a 8 > 0 such that 111 - 81 bll 00 < 1, whence
III - 8I T(b) II = IlT(1 - 81 b) II :s 111 - o,bll oo < 1.
Consequently, 8I T(b) and thus also T(b) = T(a) - AI is invertible.•
Sectoriality. A function a E Loo is said to be sectorial if 0 (j. conv R(a). The previous theorem says that Toeplitz operators with sectorial symbols are invertible. It is easily seen (Figure 7) that a E Loo is sectorial if and only if
a E GLoo and dist(a/lal, C) < 1, (1.28)
where (a/lal)(t) := a(t)/la(t)l, C stands for the constant functions, and the distance is measured in the Loo norm, i.e.,
dist(f, C) = inf Ilf - cll oo .
cEC
Local sectoriality. Let a E LOO and T E T. Given a subarc U c T, we denote by Loo(U) the essentially bounded functions on U and we define Ru (a) as the essential range of the restriction a IU, that is, as the spectrum of alU in the Banach algebra Loo(U). Finally, we let UT denote the collection of all arcs U C T containing T, and we set
RT(a):= n Ru(a).
UEUT
The set R T(a) is called the local essential range of a at T. The points in R T(a) are also referred to as the essential cluster points of a at T. If a E PC, then obviously
RT(a) = {a(T - 0), a(T + O)}. (1.29)
The function a is called locally sectorial at T E T if 0 (j. cony R T(a) and it is said to be locally sectorial on T if 0 (j. cony R T(a) for every T E T (see Figure 8).


 22 1. Infinite Matrices
3 1.5
2 ,, 0.5 ,
I
conv R(a) 0 ,
"
-0.5
0 " ,,
-1 .. _----- ... Fig. 7a Fig.7b
-1 -1.5
-1 0 2 3 -1 0
Figure 7a tells us why a function a is called sectorial if 0 rf- conv R(a): in that case R(a) is contained in some open sector with the vertex at the origin and with an opening less than 1r. If conv R(a) is as in Figure 7a, then dist(a/lal, C) = Ila/lal-l'lloo with I' as in Figure 7b.
For f E LOO and 7 E T, put
distr(f, C) := inf f1T(f - c).
cEC
Thus, (!r(f) is the "local LOO norm" of fat 7, while distr(f, C) is the "local
distance" of fat 7 to the constants. A little thought reveals that a E GLoo is locally sectorial at 7 E T if and only if
distr(a/lal, C) < 1.
Lemma 1.19. If f E Loo, then
dist(f, C) = maxdistr(f, C),
rET
(1.30)
(1.31 )
where
dist(f, C) := inf{llf - cll oo : c E C}.
The maximum in (1.31) is attained at some 70 E T.
Proof. The estimate "2" in (1.31) is obvious. To prove the reverse estimate, fix c > O. For each 7 E T, there are a number I'r E C and an arc Ur E Ur such that
IlflUr -l'rlluX>(UT ) < distr(f, C) + c.
Choose finitely many Uj := Urj and I'j := I'rj such that T is covered by the union of the Uj's. There exist functions <Pj E C such that
O:S 'Pj :s 1, SUPP'Pj C Uj , L 'Pj = 1. j


 1.7 Locally Sectorial Symbols 23
1.5 1.5
2 @) @) 61
3
0.5 0.5 @) @}l
00
-0.5 -0.5
6 F~8b3@) @~
4
-1 -1
Fig. 8a 5 -1.5 -1.5
-1 0 -1 0
If T is divided into 6 arcs as in Figure 8a and if the images of these arcs are as in Figure 8b, then a is locally (but not globally) sectorial.
Since
Ik -L~j~jIL = IkL~j -L~j~jlloo
J JJ
= II L(f - ~j)~jlloo ~ mr IlflUj - /'jllu"'(uj)'
J
we get the estimate "~" in (1.31). The map T f-t (!r(f) is easily seen to be upper semicontinuous. This implies that the map T f-t distr(f, C) is also upper semicontinuous, by virtue of which the maximum in (1.31) is attained.•
Corollary 1.20. If a E Loo is locally sectorial on T, then there exist a function c E GC and a sectorial function s E G L00 such that a = cs.
Proof. Put u = a/lal. Combining (1.30) and Lemma 1.19, we obtain that
dist (u, C) < 1. Let c E C be any function such that Ilu - cll oo < 1. Because
u is unimodular, we have III - u-1c11 00 = Ilu - cll oo < 1, which shows that
a := u-1c is sectorial. In particular, c EGG. Furthermore, we can write
a = clala- 1 and it is clear that s := lala- 1 is sectorial together with a .•
Theorem 1.21 (Simonenko). If a E Loo is locally sectorial on T, then T(a) is Fredholm on [2.
Proof. Write a = cs as in Corollary 1.20. From Proposition 1.12 we infer that T(a) = T(c)T(s) + H(c)H(s). The operator H(c) is compact in view of the (sufficiency part of) Theorem 1.16, the operator T(c) is Fredholm due to Theorem 1.17, and the operator T(s) is invertible owing to Theorem 1.18. •


 24 1. Infinite Matrices
Winding number of a locally sectorial function. Let a E LOO be locally sectorial on T and let a = cs with a function c E GC and a sectorial function s. From Theorem 1.17 and the proof of the preceding theorem we see that
-wind(c,O) IndT(c) = IndT(c)+ IndT(s)
Ind T(c)T(s) = Ind T(a).
Thus, if a = CIS1 = C2S2 with C1, C2 E GC and with sectorial functions Sl, S2, then wind(c1'0) = -Ind T(a) = wind(c2' 0). In other words, the winding number wind(c, 0) is independent of the special representation a = cs as in Corollary 1.20 (also see Figure 9). We denote this number by wind(a,O) and so have the following result.
Theorem 1.22 (Simonenko). If a E Loo is locally sectorial on T, then
Ind T(a) = -wind(a, 0) .•
2.--------.--,---.--------.--,------,.-------,
1.5
0.5
o
-0.5
-I
-1.5
2
0.5 1.5
o
-I -0.5
-2 L - _ - ' -_ _-'--_ _' - - _ - ' -_ _-'--_----J_ _--'
-1.5
The winding number with respect to the origin of the locally sectorial symbol whose essential range is indicated in Figure 9 equals 2.
Notes. Theorem 1.18 appeared explicitly in the Brown-Halmos paper [43] for the first time, but it is implicit also in Simonenko's papers [158], [161]. Theorems 1.21 and 1.22 are Simonenko's [158], [161]. They were also obtained independently and by different methods by Devinatz [53], Douglas


 1.8 Discontinuous Symbols 25
and Widom [63], and Douglas and Sarason [62]. One can show that T(a) is Fredholm if a is locally sectorial in a much weaker sense than above, e.g., if a is locally sectorial over the fibers of QC (R. Douglas) or the maximal antisymmetric sets of C +Hoo (S. Axler); for more about this topic see [39, Sections 2.75-2.91].
1.8 Discontinuous Symbols
In this section we collect some results on the spectra of Toeplitz operators with discontinuous (but not necessarily locally sectorial) symbols. A detailed discussion of this topic is in [39].
Piecewise continuous symbols. Let first a E PC be a piecewise continuous function (recall Example 1.7). We denote by a#(T) the closed continuous and naturally oriented curve which results from the essential range of a by filling in the line segment [a(t - 0), a(t + 0)] between the endpoints a(t - 0) and a(t + 0) of each jump. For A E C\a#(T), we let wind(a#, A) stand for the winding number of a#(T) with respect to A (see Figure 10).
3r---.------.-----.-----, 3r---.------.-----.-----,
2
R(a)
2
00
-I Fi~ -1
-2 -2
Fig. lOb -3 -3
-2 0 2 -2 0 2
The essential range R(a) of a piecewise continuous function (Figure lOa) and the corresponding curve a#(T) (Figure lOb).
The following beautiful result was discovered by many people, including Calderon, Spitzer, Widom, Devinatz, Gohberg, Krupnik, and Simonenko.
Theorem 1.23. Let a E PC. The operator T(a) is Fredholm on l2 if and
only if 0 rt a# (T). In that case
Ind T(a) = -wind(a#, 0).


 26 L. Infinite Matrices
Thus. sPess T(a)
spT(a)
a#(T),
a#(T) U {A E C\a#(T): wind(a#,A) -=1= a}.
P1'Oof If a 1- a#(T) then, by (1.29), a is locally sectorial on T. It is not difficult to verify that wind(a,O) = wind(a#,O), where wind(a,O) is understood as in Theorem 1.22. Therefore Theorems 1.21 and 1.22 imply the Fredholmness of T(a) and the index formula. That T(a) cannot be Fredholm if a E a#(T) can be shown by the index perturbation argument of the proof of Theorem 1.15.•
Example 1.24: Cauchy-Toeplitz matrices. For "Y E C\Z, define'l/J'Y E PC by (1.10) as in Section 1.2:
'l/J'Y(eiO ) = (11"/sin1l""'f)ei7r'Ye-i'Yo, () E [0,211").
From (1.11) we infer that
1
a E 'l/J; (T) {==? e27ri'"( E (-00, 0) {==? Re"Y - 2 E Z.
As () moves from a to 211", the argument of e-i'"(O changes from a to - 211" Re "Y. This shows that for k E Z,
11
k - 2" < Re"Y < k + 2 ==? wind('l/J;,O) =-k
(see also Figure 11). Hence, Theorem 1.23 gives that
11
T('l/J'Y) is Fredholm of index k {==? k - 2 < Re"Y < k + 2'
In particular, T('l/J'Y) is invertible if and only if IRe"Yl < 1/2.•
5 Fig. 11a 5 Fig. lIb
0 D0
-5 -5
-5 0 5 -5 0 5
In Figure 11 we see sPess T( 'l/J'Y) for "Y = 0.8 and "Y = 0.4 (Figure 11a) and for "Y = 3.25 + 0.2i (Figure lIb).


 1.8 Discontinuous Symbols 27
Two general results. Things are more complicated for symbols beyond PC, Le., for symbols in £OO\PC. We have the following two very useful theorems.
Theorem 1.25 (Hartman-Wintner). Ifa E £00, then
R(a) C sPess T(a).
From Theorems 1.18 and 1.25 we see that both sPess T(a) and spT(a) are always included between R(a) and convR(a).
Theorem 1.26 (Douglas-Widom). If a is in £00, then the two spectm SPess T(a) and spT(a) are connected sets.
4 R(a) 4
22
00
-2 -2
-4 Fig. 12a -4 Fig.12b
-5 0 5 -5 0 5
Figure 12a shows the essential range R(a) of a function a in PQC which has an oscillating discontinuity. The essential spectrum sPess T(a) is plotted in Figure 12b. It is clearly seen that SPess T(a) is a connected set. For PQC, see [39], for example.
Selfadjoint Toeplitz operators. The Toeplitz operator T(a) (a E £00) is selfadjoint if and only if an = a- n for all nEZ, which is the case if and only if a is real-valued. Combining Theorems 1.18, 1.25, 1.26 we arrive at the following result.
Theorem 1.27 (Hartman-Wintner). If a E £00 is real-valued, then
sPess T(a) = spT(a) = convR(a).
There is a simple direct proof of this theorem. It suffices to consider the case where a is not constant. If A rt conv R(a), then a - A is sectorial and hence T(a) - AI = T(a - A) is invertible. So suppose A E convR(a), put b = a - A, and assume T(b) is Fredholm. Let Ind T(b) = x. Since b is


 28 1. Infinite Matrices
real-valued, we have
Ind T(b) = Ind T(b) = Ind T*(b) = -x,
which implies that x = O. Theorem 1.10 therefore shows that T(b) is invertible. Let x E l2 be the solution ofthe equation T(b)x = eo where (eoh = 1 and (eo)n = a for n 2: 2. Denoting by f E H 2 the function
f(t) = Xl + X2t + x 3e + ... (t E T),
we see that bf = 1 + g with g E H~ (recall (1.15)). Thus, if n 2: 1, then
Since blfl 2 is real-valued, it follows that all Fourier coefficients with nonzero
index of blfl 2 must be equal to zero. Consequently, blfl 2 = (a - A)lfl 2 is
some constant c E R. If c = 0, then a = A a.e. because Ifl2 =I- a a.e. by
the F. and M. Riesz theorem. This case was excluded. Hence c =I- o. If A is an inner point of the segment conv R(a), then a - A changes its sign
and therefore (a - A)lfl 2 cannot be a nonzero constant. Thus, every inner point of conv R(a) belongs to sPess T(a). As sPess T(a) is a closed set, we conclude that sPess T(a) = conv R(a) .•
Triangular Toeplitz matrices. For such matrices we have the following result (also see Figure 13).
Theorem 1.28 (Wintner-Douglas). Let a E Hoc. The operator T(a) is invertible on l2 if and only if a-1 E Hoc, and the operator T( a) is Fredholm on l2 if and only if a-1 E C + HOC := {c + h : c E C, h E HOC}.
General symbols. Recall that GHoc stands for the set of all functions a E HOC which are invertible in HOC. Every function a E HOC can be analytically extended into the complex unit disk D := {z E C : Izl < I}.
The analytic extension a of a is given by a(z) = 2::~=o anzn where {an}~=o is the sequence of the Fourier coefficients of a. One can show that
GHOO = {a E H oo : inf la(z)1 > O}.
zED
The following theorem provides us with invertibility criteria for Toeplitz operators with general symbols in Loo. Since always R(a) c spT(a), we may without loss of generality assume that a is invertible in L OO •


 1.8 Discontinuous Symbols 29
3.--------.-----.----.---------.-----.----.-----,
Fig. 13 2
0
-1
-2
-3
-4-3 -2 -1 0 2 3 4
In Figure 13 we picked an analytic polynomial a E HOO and plotted ti(rT) for r = k/50 (k = 0,1, ... ,50). Thus, Figure 13 indicates tieD) = spT(a). Although the symbol at hand is continuous, Figure 13 nicely illustrates the invertibility part of Theorem 1.28. With respect to what follows in the forthcoming chapters, we also remark that the spectrum of every principal n x n section Tn(a) of T(a) is the singleton marked by * in the center of Figure 13. Clearly, sp Tn (a) does not at all mimic sp T( a) as n -> 00.
Theorem 1.29 (Widom-Devinatz). Suppose a E GLoo . Then the following are equivalent:
(i) T(a) is invertible on l2,
(ii) T(a/lal) is invertible on l2,
(iii) distL=(a/lal,GH OO ) < 1, i.e., there exists an h E GHoo such that
Ila/ial - hll oo < 1,
(iv) a/lal = hs where h E GHoo and s E Loo is sectorial.
Note that the equivalence (i) ¢? (ii) tells us that invertibility of Toeplitz operators is solely determined by the "argument" of the symbol. Of course, (iii) and (iv) are in general difficult to check. In a sense, we can say that results like Theorems 1.17 or 1. 23 represent verifiable necessary and sufficient conditions for (iii) and (iv) to be valid.


 30 1. Infinite Matrices
Notes. As for Theorem 1.25, we remark that Hartman and Wintner [98] showed that a is invertible in L= ifT(a) is invertible, while Simonenko [161] observed that a is invertible in L= if T(a) is merely known to have closed range. The connectedness of spT(a) was first proved by Widom [183], the connectedness of sPess T(a) is due to Douglas [59, Theorem 7.45]. Theorem 1.27 was established in [98]. The H= part of Theorem 1.28 is already in [192], the C + H= version of Theorem 1.28 was obtained by Douglas [58], [59, Corollary 7.341. Theorem 1.29 goes back to Widom [181] and Devinatz [53]. Full proofs of the results of this section can also be found in [39]


 2
Finite Section Method and Stability
2.1 Approximation Methods
Finite section method. Let A = (ajk),rk=l be an infinite matrix and suppose A generates a bounded operator on [2. In order to solve the equation Ax = y, i.e., the infinite linear system
we consider the truncated systems
(2.1 )
(2.2)
To abbreviate notation, let Pn be the projection on [2 acting by the rule
The system (2.2) then takes the form
PnAx Cn ) = PnY (x Cn ) E 1m Pn ); (2.4)


 32 2. Finite Section Method and Stability
here and in what follows, we freely identify 1m Pn , the image of Pn , with
en. Since Pnx(n) = x(n) for x(n) E 1m Pn , we might also write
for (2.4). The matrix
may be identified with the restriction of PnAPn to 1m Pn :
For obvious reasons, the replacement of (2.1) by (2.2) is called the finite section method.
If A = T(a) (a E LOO) is a Toeplitz matrix, the finite section method leads to solving the systems Tn(a)x(n) = PnY where
a_(n-l) )
a_(n-2)
..
ao
(2.5)
The finite section method is a special case of more general approximation methods. For example, if A = T(a)T(b) is the product of two Toeplitz matrices, two possible replacements of the equation Ax = yare
In the first case we are considering the finite section method, but in the second case we have something different.
General approximation sequences. Suppose we are given any sequence {An};:O=1 of n x n matrices An. On identifying en and 1m Pn and on regarding An as AnPn , we can think of An as given on all of 12 . We call {An} an approximating sequence for some operator A E B(12) if AnPn converges strongly to A on 12 , Le., if
for every x E 12 . Clearly, {PnAPnIIm Pn } is always an approximating sequence for A.
We write A E II{An} and say that the approximation method {An} (and the finite section method in case An = PnAPnlIm Pn ) is applicable to A if


 2.1 Approximation Methods 33
(i) the matrices An are invertible for all sufficiently large n, say for
n:::: no;
(ii) for every y E l2 the (unique) solutions x(n) Elm Pn of Anx(n) = Pny (n :::: no) converge in l2 to a solution x E l2 of the equation Ax=y.
The following theorem is also known as the uniform boundedness principle. It plays a fundamental role in numerical analysis.
Theorem 2.1 (Banach-Steinhaus). If {An}~=1 is any sequence of operators An E l3UZ) such that {AnX}~=1 is a convergent sequence in l2 for every x E l2, then SUPn>O IIAnl1 < 00, the operator A defined by Ax := limn--->oo Anx is bounded on l2, and
IIAII::; liminfllAnll·
n-+oo
A proof of this theorem is in every text on functional analysis. Here is a first application of the Banach-Steinhaus theorem.
Proposition 2.2. Let A E l3(l2) and let {An} be an approximating sequence for A. Then A E II{An} if and only if A is invertible, the matrices An are invertible for all sufficiently large n, and A~1 (:= A~1 Pn ) converges strongly to A -1 .
Proof. The "if" portion is trivial. Now suppose A E II{An }. The "only if" part will follow as soon as we have shown that A is invertible. By the definition of II{An }, the operator A is surjective. Since, also by the definition of II{An }, the sequence {A~1 PnY}n~no is convergent for every y E l2, Theorem 2.1 implies that
M:= sup IIA~1Pnll < 00.
n~no
Thus, if x E l2 and n :::: no,
IIPnxl1 IIA~1 AnPnxl1 = IIA~1 PnAnPnxl1
< IIA~1 PnllllAnPnxl1 ::; MIIAnPnxll. (2.6)
As AnPnx --+ Ax, it follows that Ilxll ::; MIIAxl1 for all x E l2, which shows that A is injective.•
Note that, in particular, no method {An} is applicable (in the above sense) to A in case A is not invertible.
Stable approximation sequences. From the basic course in numerical analysis we know the principle
convergence = approximation + stability. (2.7)


 34 2. Finite Section Method and Stability
In the following we need not be worried about approximation, because we will always require that {An} be an approximating sequence for A. What about stability? One says that a sequence {An}~=l of n x n matrices An is stable (or uniformly invertible) if An is invertible for all n large enough,
for n ~ no say, and
sup IIA;;:lll < 00.
n:;::no (2.8)
Recall that II A;-lll := II A;-l Pn II. In order to avoid the inconvenient no, we put IIA;;:lll = 00 in the case where An is not invertible.
With this convention, we may write (2.8) in the form
lim sup II A;;: 1 II < 00.
n->oo
(2.9)
If {An} is a stable sequence, then the sequence {A~} of the adjoint matrices (operators) is also stable. However, if {An} is an approximating sequence for A, then {A~} need not be an approximating sequence for the adjoint operator A *. For example, if
(2.10)
then An converges strongly to the shift operator
as n --> 00, while A~ does not at all converge strongly.
Proposition 2.3. Let A E BW) and let {An} be an approximating sequence for A.
(a) If {An} is stable, then the operator A is injective and 1m A is a closed subspace of 12 •
(b) If {An} is stable and, in addition, {A~} is an approximating sequence for A *, then A is invertible.
Proof (a) From (2.8) and (2.6) we get Ilxll ~ MllAxl1 for all x E 12 . This implies that A is injective. Moreover, ifAxn --> y, then
hence X n --> x and thus y = Ax, which shows that 1m A is closed.
(b) This follows from part (a) and the fact that our additional hypothesis yields the estimate Ilxll ~ MIIA*xll for all x E 12 .•


 2.1 Approximation Methods 35
Note that if An is as in (2.10), then {An} is stable but the strong limit A = T(Xl) of An is not invertible. This reveals that in general the conclusion of Proposition 2.2(a) cannot be sharpened.
Here is what (2.7) states in our context.
Proposition 2.4. Let A E 8(l2) and let {An} be an approximating sequence for A. Then A E II{An } if and only if A is invertible and {An} is a stable sequence.
Proof If A E II{An}, we deduce the invertibility of A and the stability of {An} from Proposition 2.2 and Theorem 2.1. Conversely, suppose A is invertible and {An} is stable. Then for each y E l2,
the second term on the right goes to zero because Pn ---. I strongly, and the first term on the right is
since AnPnA- 1 ---. AA- 1 = I strongly.•
Propositions 2.2 and 2.4 do not tell us anything that might solve the question whether the finite section method (for example) is applicable to a given concrete operator. However, they reveal the heart of the problem: we have to study the stability of the sequence {PnAPn 11m Pn }.
Example 2.5. Let A be an infinite matrix which contains exactly one unit in every row and every column. Then A is a unitary operator on l2 and hence invertible. If A is given by
U
100
1
000
A= 0 0 1 ... , 0 1 0 ...
then A is such a matrix (note that A is a block diagonal Toeplitz matrix). The last row of P2k+ 1 AP2k+ 111m P2k+1 (k = 0, 1, 2, ... ) consists only of zeros. Thus, although A is invertible, the matrices PnAPnllm Pn are not invertible whenever n is odd. By Proposition 2.2, the finite section method is not applicable to A .•
Example 2.6. We now slightly modify the matrix of the previous example: let {cn}~=o be a sequence of numbers Cn E (0,1/2] converging to zero and


 36 2. Finite Section Method and Stability
put
( <0
100
1
A~ J co 0 0 ...
0 Ci 1 0 1 Ci
(this is a compactly perturbed block diagonal Toeplitz matrix). It is readily seen that
for c E (0,1/2]. Thus, A is invertible and IIA-111 :::; 2. Clearly, An PnAPnlImPn is invertible for every n ::::: 1. If n is even, then IIA~111 :::; 2,
while if n = 2k + 1 (k ::::: 0) is odd, then IIA~lll ::::: lick' Consequently, although A and all the truncations An are invertible, the norms IIA~111 are not uniformly bounded. From Proposition 2.4 we infer that the finite section method is not applicable to A. •
Treil's theorem. Let a E UXJ and consider the infinite Toeplitz matrix T(a) and its finite sections Tn(a) (n ::::: 1) given by (2.5). Since {Tn (a)} and {T~(a)} = {Tn (a)} are approximating sequences for T(a) and T*(a) = T(a), respectively, we obtain from Proposition 2.3 the implication
{Tn (a) } is stable ===} T(a) is invertible.
Is the reverse implication also true? Here is the answer.
Theorem 2.7 (Treil). There exist a E L OO such that T(a) is invertible but {Tn(a)} is not stable.
Although the finite section method for Toeplitz operators has extensively been studied since the 1960s, this result was established by Treil [172] only in 1987. This fact uncovers the point of the matter: the construction of a symbol a as in Theorem 2.7 is rather difficult, because for large classes of symbols a the invertibility ofT(a) indeed implies the stability of {Tn(a)}. We will not give a proof of Theorem 2.7 here; full proofs are in [172], [39, Theorem 7.92], and [28]. The latter paper contains explicitly given symbols a for which T(a) is invertible but {Tn (a)} is not stable: this is, for example, the case if a is the almost periodic function
where f is 21f-periodic on Rand f(x) = 21xl for Ixl :::; 1f. Note that
8( 1 1 )
f(x) = 1f -:; cosx + 32 cos3x + 52 cos5x +... , (2.11)


 2.2 Continuous Symbols 37
which shows that f, the "stretched argument" of a, has an absolutely convergent Fourier series (see also Figure 14).
7,-----.------,----,----.,------,----,----.,-------,
6
5
4
3
2
o
Fig. 14
567
4
3
2
o
-I L--_--'-_----l..._ _'--_--'-_----l..._ _' - - _ - - ' - _ - - '
-I
Figure 14 shows the function (O,27r) --+ R, () f--+ f(-cot(()/2)) with f as in (2.11) and thus the argument of a discontinuous symbol a generating an invertible Toeplitz operator T(a) for which {Tn (a)} is not stable.
2.2 Continuous Symbols
As intimated in the end of the previous section, the sequence {Tn(a)} is stable for large classes of invertible Toeplitz operators T(a). In this section we prove that this is true if a E C. In what follows we will frequently make use of the following simple, well known, but basic lemma.
Lemma 2.8. If K is a compact operator and B n --+ B strongly, then BnK --+ BK uniformly, i.e., IIBn K - BKII --+ O.
Proof Let c > O. Since K maps the closed unit ball {x : IIxll :S I} to a set whose closure is compact, there are Xl, ... , XN in the closed unit ball such that for every X on the unit sphere we can find an Xj satisfying IIKx - KXjl1 :S c. Clearly, the norm IIBnKx - BKxl1 can be estimated


 38 2. Finite Section Method and Stability
from above by
IIBnllllKx - KXjl1 + IIBnKxj - BKxj11 + IIBlllIKxj - KxlI :::; IIBnlle: + IIBnKxj - BKxj11 + IIBIIe:·
Theorem 2.1 implies that IIBnl1 :::; M < 00 for all n, and because B n
converges strongly to B, the norms IIBnKxj - BKxj11 are less than e: for all j and all sufficiently large n. Thus, if n is large enough, then
IIBnKx - BKxl1 :::; (M + 1 + IIBII)e: = (M + 1 + IIBII)cllxll
whenever Ilxll = 1. •
The following well-known fact has been shown by various authors to be extremely useful in several contexts. We learned it from A.V. Kozak in the late 1970s (private communication).
Lemma 2.9. Suppose X is a linear space, P and Q are complementary
projections on X (i. e., p 2 = P, Q2 = Q, P + Q = 1), and A is an invertible operator on X. Then the compression P API 1m P is invertible on 1m P if and only if the compression QA-1QllmQ is invertible on ImQ. In that case
Proof. We have
PAP(PA- 1P _ PA-1Q(QA-1Q)-lQA- 1p)
= PA(I - Q)A- 1P - PA(I - Q)A-1Q(QA-1Q)-lQA-1p
= P - PAQA-1p- 0 + PAQA-1p = P,
and similarly we get (PA- 1P - PA-1Q(QA-1Q)-lQA- 1P)PAP = P .•
As a first consequence of Lemma 2.9 we record the following observation, which shows that the truncations of the inverse of Toeplitz matrices are always stable. Recall that Pn is defined by (2.3).
Theorem 2.10. Let a E LOO and suppose the operator T(a) is invertible. Then {PnT-1(a)Pnllm Pn } is stable.
Proof Let Qn := 1- Pn. Since QnT(a)QnllmQn has the same matrix as T(a), we see that QnT(a)QnllmQn is invertible for all n ~ 1 and that
Lemma 2.9 therefore implies that PnT- 1(a)Pnllm Pn is invertible for all n ~ 1 and that the norm of the inverse is at most
IIPnT(a)Pn - PnT(a)Qn(QnT(a)Qn)-lQnT(a)Pnll
:::; IIT(a)11 + IIT(a)IIIIT-1(a)IIIIT(a)ll· •


 2.3 Asymptotic Inverses 39
The following theorem is a classical result of Gohberg and Feldman [80]. The proof given below is from [35, Section 3.10].
Theorem 2.11 (Gohberg-Feldman). If a E C and T(a) is invertible, then {Tn (a)} is stable.
Proof. By Proposition 1.12, T(a)T(a- 1) = 1- H(a)H(a- 1) and thus,
T-1(a) = T(a- 1) + T-1(a)H(a)H(a- 1) =: T(a- 1) + K.
The operator K is compact due to (the sufficiency part of) Theorem 1.16. Since Qn ----f 0 strongly, we deduce from Lemma 2.8 that
whence
The operator QnT(a-1)QnIImQn has the same matrix as T(a- 1), and as T(a-I) is invertible together with T(a) (Theorem 1.17), it follows that QnT-1(a)QnIImQn is invertible for all sufficiently large n and that for every c > 0 there is an no (c) such that
for all n ;::: no(c). For these n we obtain from Lemma 2.9 that Tn(a) = PnT(a)PnIImPn is invertible and that (PnT(a)pn )-l Pn equals
Since the norm of this operator does not exceed
we see that {Tn (a)} is stable.•
2.3 Asymptotic Inverses
In addition to the projections Pn and Qn = 1- Pn , we need the operators Wn (n ;::: 1) which are defined on l2 by
Obviously,


 40 2. Finite Section Method and Stability
Recall that a(t) := a(l/t) (t E T). It can also be readily verified that W n
converges weakly to zero, i.e., (Wnx,y) ---> °as n ---> 00 for every x,y E 12.
The following proposition is the finite section analogue of Proposition 1.12.
Proposition 2.12 (Widom). If a, b E Loo , then
PnT(a)QnT(b)Pn = WnH(a)H(b)Wn , (2.12)
Tn(ab) = Tn (a)Tn(b) + Pn H(a)H(6)pn + WnH(a)H(b)Wn . (2.13)
Proof. Let n(t) := t k (t E T). Then for n ~ 1,
T(X-n) : {Xl, X2, } I---t {Xn+l' Xn+2, },
T(Xn) : {XI,X2, } I---t {O, ... , O,XI,X2, },
the latter sequence containing n zeros. An easy computation shows that
Since T(X-n)T(Xn) = I, we therefore get
PnT(a)QnT(b)Pn = WnWnT(a)QnQnT(b)WnWn
= WnPnH(a)T(X-n)T(Xn)H(b)PnW n = WnH(a)H(b)Wn ,
which is (2.12). By Proposition 1.12,
and using (2.12) we obtain
PnT(a)T(b)Pn = PnT(a)PnT(b)Pn + PnT(b)QnT(b)Qn
= Tn(a)Tn(b) + WnH(a)H(b)Wn .•
Let a E L OO and suppose T(a) is invertible. Then a E GLoo due to Theorem 1.25. Since T(a) is the transposed operator of T(a), the operator T(a) is also invertible. Thus, the two operators
K(a) := T-I(a) - T(a- l ) and K(a):= T-I(a) - T(a- 1 ) (2.14)
are well-defined bounded operators.
Lemma 2.13. If a E LOO and T(a) is invertible, then
(PnT-I(a)Pn + WnK(a)Wn)Tn(a)
= Pn - PnK(a)QnT(a)Pn - WnK(a)QnT(a)Wn, (2.15)
Tn(a) (PnT-1(a)Pn + WnK(a)Wn )
= Pn - PnT(a)QnK(a)Pn - WnT(a)QnK(a)Wn. (2.16)


 2.3 Asymptotic Inverses 41
Proof. By (2.12) and Proposition 1.12,
PnT(a-1)QnT(a)Pn = WnH(ii-1)H(a)Wn
= Wn{I - T(ii-1)T(ii))Wn = WnK(ii)T(ii)Wn
= WnK(ii)WnT(a)Pn + WnK(ii)QnT(ii)Wn .
Thus,
On the other hand,
PnT-1(a)PnT(a)Pn = Pn - PnT-1(a)QnT(a)Pn
= Pn - PnK(a)QnT(a)Pn - PnT(a-1)QnT(a)Pn. (2.18)
Adding (2.17) and (2.18) we arrive at (2.15). The identity (2.16) results from (2.15) after passage to transposed matrices.•
Asymptotic inverses. Formulas (2.15) and (2.16) are useful if their righthand sides can be shown to be of the form Pn + Dn with \\Dnll - 0 as n - 00. In that case they provide an asymptotic inverse of the sequence {Tn(a)}~=l' i.e., a sequence {Bn}~=l of n x n matrices B n such that
and
sup IIBnl1 < 00
n;:::l (2.19)
Note that if (2.19) and (2.20) are valid, then {Tn (a)} is necessarily stable and
T;l(a) = Bn + Cn with IICnl1 - 0 as n - 00. (2.21)
Indeed, if BnTn(a) = Pn + Dn where IIDnl1 - 0, then there is an no such
that IIDnll < 1/2 for all n ~ no. It follows that Pn + Dn is invertible for
n ~ no and that T;l(a) = (Pn + Dn)-l B n . Since II(Pn + Dn)-lll < 2, we infer from (2.19) that
which proves the stability of {Tn (a)} and also gives the representation (2.21) with Cn = -Dn T;l(a). Clearly, (2.21) always implies (2.20), independently of whether (2.19) holds or not. Here is an asymptotic inverse of {Tn (a)} in case the symbol a is continuous.


 42 2. Finite Section Method and Stability
Theorem 2.14 (Widom). Let a E C and suppose T(a) is invertible. Then for all sufficiently large n,
PnT-1(a)Pn + WnK(a)Wn + C n
Tn(a- 1) + PnK(a)Pn + WnK(a)Wn + Cn,
(2.22)
(2.23)
where K(a) = T-1(a) - T(a- 1) and K(a) = T- 1(a) - T(a- 1) are compact
and IICnl1 ----> 0 as n ----> 00.
In particular, under the hypothesis of the theorem, (2.19), (2.20), and (2.21) are valid with
PnT-1(a)Pn + WnK(a)Wn
Tn(a- 1) + PnK(a)Pn + WnK(a)Wn . (2.24)
Proof. Consider the identities (2.15) and (2.16). By Proposition 1.12,
K(a) = H(a-1)H(a)T-1(a) and K(a) = H(a-1)H(a)T-1(a). (2.25)
The continuity of a gives the compactness of all occurring Hankel operators (Theorem 1.16). Hence, K(a) and K(a) are also compact. Since Qn ----> o strongly, Lemma 2.8 shows that IIQnK(a)11 ----> 0 and IIQnK(a)11 ----> o.
Passing to adjoints we see that IIK(a)Qnll ----> 0 and IIK(a)Qnll ----> 0, too. Consequently, on defining B n by (2.24) we deduce from Lemma 2.13 that (2.19) and (2.20) and thus also (2.21) hold.•
Second proof of Theorem 2.11. From (2.22) we see that if a E C and T(a) is invertible, then {Tn (a)} is stable. Moreover, it follows that for every E > 0 there is an no (E) such that
for all n 2': no(E) .•
Entries of the inverses. Of course, (2.22) and (2.23) provide information about the jk entry of T;l(a). Given a matrix A, we denote its jk by A jk or [A]jk' Clearly, Ajk = (Aek, ej) where en is the (finite or infinite) sequence having a unit at the nth position and zeros at all other positions. If a E Loo, T( a) is invertible, and {Tn (a)} is stable, then Propositions 2.2 and 2.4 imply that
IIT;l(a)ej - T-1(a)ejll ----> 0 as n ----> 00
for each j. Thus, the jth column of T;; 1 (a) (extended by zeros to an element of l2) converges in l2 to the jth column of T-1(a). In particular,


 2.3 Asymptotic Inverses 43
for each pair (j, k). Define K(a) and K(ii) by (2.14) and write
Clearly,
[T-1(a)Lk = (a-l)j_k + gjk·
If a is smooth, then (2.26) can be improved. Here is an example of such a more precise estimate.
Theorem 2.15. Let a E C and let T(a) be invertible. In addition, suppose
(2.27)
for some a > o. Then
uniformly with respect to (j, k) E N 2 . Further, for each bounded subset n of N 2 there exists a constant Cn = Cn(a) such that
(2.29)
for all (j, k) E n and all n ;::: 1.
Proof Let WO denote the set of all functions a E C satisfying (2.27). It is well known that WO is a Banach algebra with pointwise algebraic operations and the norm lIall := LnEZ(1 + Inl)°lanl and that if a E Wct and a has no zeros on T, then a-I E Woo Given a function f E LOO(T), we denote by snf the (n -1)st partial sum of its Fourier series. If f E W ct , then
Ilf - snflloo ::; L Ifd ::; ~ L IWlf11 = o(l/nO).
n
111~n Ill~n
Since QnH(f) = QnH(f - snf), we get
IIQnH(a-I)11 ::; lla- l - sna-1lloo = o(l/nct ),
IIQnH(ii-I)11 ::; llii- 1 - snii-1lloo = o(l/nO).
Thus, by (2.25),
With Bn given by (2.24) we therefore deduce from (2.16) that


 44 2. Finite Section Method and Stability
and since {Tn(a)} is stable, it follows that T;l(a) = B n + en with
As [Bn]jk = [T-1(a)]jk + hn+l-j,n+l-k, we see that (2.28) holds uniformly with respect to (j, k) E N 2 .
By Proposition 1.12, K(a) = T-1(a)H(a)H(a- 1). Hence
I(VVnK(a)VVnek,ej)1
= I(T-1(a)H(a)H(a- 1)en+l-k, en+l-j) I
~ IIT-1(a)H(a)IIIIH(a-1)en+l_kll·
Let b := a-I. Then bE VVQ and thus,
M 2 := L Inj 2Q lbn l2 < 00.
nEZ
Consequently, for n ~ k,
IIH(a- 1)en+l_kIl 2 = L Ibn-k+tl 2 12: 1
1 M2
< "(n - k + l) 2<> Ib 12 < --;---------,--:-;:
- (n+l-k)2<>LJ n-k+1 - (n+l-k)2Q'
12: 1
whence
Ihn+1-j,n+l-kl ~ M/(n + 1 - k)<>.
For n ~ j, passage to transposed operators gives
Ihn+1-j,n+l-k! ~ M/(n + 1 - j)Q.
(2.30)
(2.31 )
Clearly, each of the estimates (2.30) and (2.31) implies the last assertion of the theorem.•
Notes. Results similar to Theorem 2.15 can be found in [136, pp. 106-107]. All other results of this section are from Widom's paper [185].
2.4 The Gohberg-Feldman Approach
The proofs of Theorems 2.11 and 2.14 given above break hopelessly down in case a is a piecewise continuous function: one can show that functions in Hoo cannot have jumps, so that H(a) is never compact if a E PC\C (recall Theorem 1.16). In this section we present the approach of Gohberg and Feldman [80] to the stability of the finite sections of Toeplitz operators with piecewise continuous symbols.


 2.4 The Gohberg-Feldman Approach 45
The following theorem shows that the applicability of the finite section method is stable under compact perturbations.
Theorem 2.16. Let A E l3W) and suppose {PnAPn } is stable. If K E
K,(l2) and A + K is invertible, then {Pn(A + K)Pn } is stable.
Proof Put An = PnAPnlIm Pn and notice first that
Pn(A + K)Pn = PnAPn (1 + A~1 PnKPn)Pn
for all sufficiently large n. Since A~ 1 Pn _ A-I strongly due to Propositions 2.2 and 2.4, we infer from Lemma 2.8 that A~I PnK converges uniformly to A-I K. The operator I + A-I K = A-I(A + K) is invertible; let us put
11(1 + A-I K)-III =: l/E. We then have for every x E l2 the estimate
EllPnxll ~ 11(1+A- IK)Pnxll
~ 11(1 + A~I PnK)Pnxll + IIA~I PnK - A-I KllllPnxll,
and the second term on the right is less than (E/2)llPnxll if only n is large enough. For these n,
(E/2)llPnxll < 11(1 + A~I PnK)Pnxll
~ IIA~IIJII(An + PnKPn)PnxlJ = IIA~IllllPn(A + K)Pnxll,
and as IJA~IIJ ~ M with some M < 00, we arrive at the inequality
(2.32)
It follows that Pn(A + K)PnIIm Pn is injective and thus invertible. More
over, (2.32) also yields the estimate II (Pn(A + K)Pn)-III ~ 2M/E, which
proves that {Pn(A + K)Pn } is stable.•
Perturbing Toeplitz operators. The idea of the Gohberg-Feldman approach is best understood for symbols in the Wiener algebra W. So assume a E Wand T(a) is invertible. Let
be a Wiener-Hopf factorization of a (recall Theorems 1.14 and 1.15). We then have T(a) = T(a_)T(a+), but the point is to consider the (invertible) operator
We have
PnAPn = PnT(a+)PnT(a_)Pn + PnT(a+)QnT(a_)Pn ,
and as PnT(a+)Qn = QnT(a_)Pn = 0, it follows that
PnAPn = Tn(a+)Tn(a_).


 46 2. Finite Section Method and Stability
Consequently, PnAPn is invertible for all n ~ 1 and
(note that Tn (b)Tn(c) = Tn(bc) ifTn(b) and Tn (c) are both upper-triangular or both lower-triangular). Because
we arrive at the conclusion that {PnAPn } is stable. We finally pass from A to T(a). By Proposition 1.12,
where K := H(a+)H(cL) is compact. Theorem 2.16 tells us that {Tn (a)} is stable. In order to extend the reasoning outlined above, we need the following simple analogue of the Brown-Halmos theorem (Theorem 1.18).
Proposition 2.17. If a E VX), then
spTn(a) c convR(a) for all n ~ 1.
If a E Loo is sectorial, then d:= dist(O,convR(a)) > 0 and
(2.33)
IIT;l(a)1I ~ ~ (1 + 1- II~~~) < ~ for all n ~ 1. (2.34)
Proof. Fix .\ E C\conv R(a) and put b := a -.\. There is a'Y E T such that the set 'YconvR(b) is contained in the set {z E C: Rez ~ d, Izi ~ Ilbll oo }. Multiplying the latter set by 0 := d/llbll~ we obtain a subset of the disk
{z E C: Iz - 11 < r} where 1':= Jl- d2/lIbll~·
Hence,
This implies the invertibility of Tn(b) = Tn(a) - .\I for all n ~ 1 and thus gives (2.33). Moreover, from (2.35) we get
IIT;l(b)11 ~ obi = 0(1 + 1') = ~ (1 +
1 - l' 1 - 1'2 d d
2 )
1- IIbll~ ,
and letting>' = 0 (i.e., b = a), we arrive at (2.34).•


 2.5 Algebraization of Stability 47
Theorem 2.18 (Gohberg-Feldman). Let a E LOO be locally sectorial on T and suppose T(a) is invertible. Then {Tn(a)} is stable.
Proof. By Corollary 1.20, we have a = cs with c E GC and a sectorial function s E GLoo. We can approximate c by functions in the Wiener algebra (e.g., by its Fejer-Cesaro means) as closely as desired. Thus, given any c > 0 there are dEW and <p E C such that c = d(I+<p) and 11<p1100 < c.
If c is small enough, then r := (1 + <p)s is sectorial together with s. Hence, a = dr with d E GW and a sectorial function r. By Proposition 1.12, T(a) = T(d)T(r) + H(d)H(f). The operator H(d) is compact (Theorem 1.16) and the operator T(r) is invertible (Theorem 1.18). Consequently, T(d) must be Fredholm of index zero. From Theorems 1.14 and 1.15 we therefore deduce that d admits a Wiener-Hopf factorization
In summary, a = d_d+r = d+rd_. Now put A:= T(d+)T(r)T(d_). Since PnT(d+)Qn = 0 and QnT(d_)Pn = 0, we obtain
The operators Tn(d+) and Tn(d_) have the uniformly bounded inverses Tn (d:t 1) and Tn (d= 1), respectively, while {Tn (r)} is stable due to Proposition 2.17. This implies that {PnAPn } is stable. Again by Proposition 1.12,
T(a) T(d+)T(rd_) + H(d+)H(fL)
T(d+)T(r)T(d_) + T(d+)H(r)H(L) + H(d+)H(fL),
and since H(L) and H(d+) are compact, Theorem 2.14 shows that {Tn (a)} is stable.•
Corollary 2.19 (Gohberg-Feldman). If a E PC and T(a) is invertible, then {Tn (a)} is stable.
Proof. Theorem 1.23 in conjunction with (1.29) says that if a E PC and T(a) is invertible (or even only Fredholm), then a is locally sectorial on T. The assertion is therefore immediate from Theorem 2.16.•
2.5 Algebraization of Stability
We now develop another approach to the stability problem for the finite sections of Toeplitz matrices. This approach allows us to give alternative proofs of Theorems 2.11 and 2.18. At first glance, the machinery constructed in


 48 2. Finite Section Method and Stability
the following seems to be unduly heavy, but this machinery will prove to be of deciding importance in the forthcoming chapters.
The big algebra. The idea of the approach is to build a Banach algebra 9 such that
{An} is stable {=? something is invertible in g.
To begin with, let F be the set of all sequences {An} = {An} ~=1 of oper
ators (matrices) An E B(lm Pn ) (~ c nxn ) for which
II{An}11 := sup IIAnl1 < 00.
n:2:1
The set F with the algebraic operations
(2.36)
and the norm (2.36) is easily seen to be a Banach algebra. An element {An} E F is invertible in F if and only if An is invertible for all n ~ 1 and SUPn>l IIA~lll < 00. Clearly, invertibility in F is not equivalent to stability, but it has undoubtedly something to do with it. Now denote by N the subset of F consisting of all {Cn } E F such that
IICnl1 ~ 0 as n ~ 00. It is not difficult to show that N is a closed two-sided ideal of F and hence we may consider the quotient algebra FIN.
Proposition 2.20. A sequence {An} E F is stable if and only if the coset {An} + N is invertible in FIN.
Proof. If {An} +N is invertible in FIN, then there is a sequence {Bn } E
F such that BnAn = Pn + Cn with IICnl1 ~ o. If IICnl1 < 1/2, then
Pn + Cn is invertible (note that Pn is the identity operator on 1m Pn ) and
(Pn + Cn )-1 B n is the inverse of An. Since
it follows that {An} is stable. Conversely, let {An} be stable. Suppose An is invertible for n 2: no· Define B n = A~l for n ~ no and B n = 0 for n < no. Then {Bn } E F and {Bn}{An } - {Pn } as well as {An}{Bn } - {Pn } belong to N .•
Note that if {Bn } +N E FIN is the inverse of {An} +N if and only if {Bn } is an asymptotic inverse of {An} in the sense of Section 2.3:
sup IIBnl1 < 00, IIAnBn - Pnll ~ 0, IIBnAn - Pnll ~ O.
n2:1
The modified algebra. Now suppose a E C and T(a) is invertible. Proposition 2.12 then gives the formula


 2.5 Algebraization of Stability 49
and a similar formula for Tn (a )Tn(a -1). Note that all occurring Hankel
operators are compact. If sequences of the form {PnK Pn + WnL Wn } with compact operators K and L would belong to N, then Proposition 2.20 would imply that {Tn (a)} is stable. However, these sequences clearly do not belong to N. SO let us replace N by the set
.:r := {{PnK Pn + WnLWn + Cn}~=l : K, L E K(l2), Ilenll ---+ O}.
Then {Tn(a- 1)} is an inverse of {Tn (a)} modulo .:r and it would be nice to have a Banach algebra S C F with the following properties:
• .:r is a closed two-sided ideal of S;
• {Tn(a)} E S for all a E L oo ;
• invertibility in the quotient algebra S /.:r has something to do with invertibility in F / N, Le., with stability.
Let S be the collection of all {An} E F for which there are two operators A and A in B( l2) such that
where the asterisk refers to the adjoint operator and ---+ denotes strong convergence. We now show that S enjoys the properties required above. First of all, it is easily seen that S is a closed subalgebra of F.
Lemma 2.21. .:r is a closed two-sided ideal of S.
Proof Obviously, .:r is a selfadjoint linear subspace of S. We now prove
that .:r is closed. Let
(2.38)
Since Wn converges weakly to zero and L is compact, it follows that LWn and thus also WnLWn converges strongly to zero. Consequently, An ---+ K and WnAn W n ---+ L strongly, whence
IIKII::; liminfllAnll, IILII::; liminfllAnll,
n-+oo n-+oo
by Theorem 2.1. Thus, if {A}/)} c .:r is a Cauchy sequence, then so are {K(j)} C K(l2) and {L(j)} C KW). We conclude that there are
K, L E KW) such that IIK(j) - KII ---+ 0 and IIL(j) - LII ---+ 0 as j ---+ 00,
which implies almost at once that there is a sequence {An} E .:r such that
II{A}/)} - {An}1I ---+ 0 as j ---+ 00. This proves that .:r is closed.
If {An} E .:r is given by (2.38) and {Bn } is any sequence in S, then
BnAn = Pn(BnPnK)Pn + Wn(WnBnWnL)Wn + BnCn ,


 50 2. Finite Section Method and Stability
and since BnPnK ---> BK and WnBnWnL ---> BL uniformly (Lemma 2.8), it results that
BnAn = PnBK Pn + WnBLWn + C~
with {C~} E N. Hence {Bn}{An } E 3. Passing to adjoints we see that {An }{ Bn } also belongs to 3 .•
Lemma 2.22. If a E Loo , then {Tn(a)} E 5, the strong limits of Tn(a) and WnTn(a)Wn being T(a) and T(ii) , respectively.
Proof This is immediate from the equalities
T~(a) = TnCa), T*(a) = T(a), WnTn(a)Wn = Tn(ii) . •
Theorem 2.23. Let {An} E 5 and denote the strong limits of An and WnAnWn by A and A, respectively. Then the following are equivalent:
(i) {An} is stable;
(ii) A and A are invertible operators and the coset {An} +3 is invertible in the algebra 5/3.
Proof (i) =} (ii). Suppose {An} is stable. Since A~ ---> A* strongly by the definition of 5, we deduce from Proposition 2.3 that A is invertible. As
the sequence {WnAnWn } is also stable. Again by the definition of the algebra 5, WnAnW n ---> A and (WnAnWn )* ---> A* strongly, which, once
more by Proposition 2.3, implies that A is invertible. From Proposition 2.4 we now deduce that
A E ll{An }, A E II{WnAnWn }, A* E ll{A~}, A* E ll{WnA~Wn}'
Suppose An is invertible for n 2': no. Put Bn = A;;-l for n 2': no and Bn = 0 for n < no. Using Proposition 2.2 we obtain
B n ---> A-l, WnBnWn ---> A-I, B~ ---> (A*)-l, WnB~Wn ---> (A*)-l.
This shows that {Bn } E 5. Since
{Bn}{An } - {Pn } ENe 3, {An}{Bn } - {Pn} ENe 3,
the element {Bn } + 3 is the inverse of {An} + 3.
(ii) =} (i). Let {Bn } + 3 be the inverse of {An} + 3 and denote by B
and 13 the strong limits of B n and WnBnWn , respectively. We have
AnBn = Pn + PnK Pn + WnLWn + Cn
with K, L E K(l2) arid IICnl1 ---> O. Taking into account that WnLWn and
WnKWn converge strongly to zero, we get AB = 1+ K and AB = I + L, which shows that
S := A-I - B = -A- IK and T:= A-I - 13 = _A- 1L


 K + AS = L + AT = 0,
2.5 Algebraization of Stability 51
are compact. Put
Then {Rn} ESC :F and
AnRn = Pn + Pn(K + AnPnS)Pn + Wn(L + WnAnWnT)Wn + Cn'
Lemma 2.8 shows that this is
Pn + Pn(K + AS)Pn + Wn(L + AT)Wn + C~,
where IIC~II --> O. As
we see that AnRn = Pn + C~. Hence, {An} + N is invertible from the
right. Analogously one can prove that {An} +N is invertible from the left. Proposition 2.20 therefore yields the stability of {An} .•
In the course of the previous proof we showed that if {Bn } + .:J is the
inverse of {An} + .:J in S / .:J, then
-I --I 
R n = B n + Pn(A - B)Pn + Wn(A - B)Wn (2.39)
is an asymptotic inverse of An, that is,
sup IIRnII < 00, IIRn A n - Pnll --> 0, IIAnRn - Pnll --> O.
n~1
Corollary 2.24. Let a E L oo and suppose T(a) is invertible. Then for {Tn(a)} to be stable it is necessary and sufficient that {Tn(a)} + .:J be invertible in S / .:J.
Proof This follows from Lemma 2.22, Theorem 2.23, and the fact that T(a) is invertible if and only if so is the (transposed) operator T(ii) .•
Third proof of Theorem 2.11. If a E GC, then (2.37) and its analogue for Tn(a)Tn(a- l ) shows that {Tn(a- 1)} +.:J is the inverse of {Tn (a)} +.:J. Theorem 2.11 is therefore an immediate consequence of Corollary 2.24.•
Moreover, Theorem 2.14 is now seen to result straightforwardly from (2.39). The real strength of Theorem 2.23 will be revealed in the forthcoming sections. This theorem reduces the stability problem for sequences in S to invertibility in the algebra S / .:J, and unlike the algebra :F/ N, the algebra S /.:J is so nice that it can be studied with the help of so-called local principles.
Notes. Proposition 2.20 is the starting point of the local approach to projection methods developed by Kozak [109J. The approach exhibited here (including the algebra S, the ideal .:J, and Theorem 2.23) is from [154].


 52 2. Finite Section Method and Stability
2.6 Local Principles
Homomorphisms and isomorphisms. Given two Banach algebras A and 13, a map cp : A --> 13 is called a Banach algebra homomorphism if cp is a bounded linear operator and
cp(ab) = cp(a)cp(b) for all a, bE A.
Bijective Banach algebra homomorphisms are referred to as Banach algebra isomorphisms.
Commutative Banach algebras. Let A be a commutative Banach algebra with identity element e. The Banach algebra homomorphisms of A into C which send e to 1 are called the multiplicative linear functionals of A. Let M denote the set of all maximal ideals of A and let M stand for the set of all multiplicative linear functionals of A. One can show that the map M --> M, cp I-t Ker cp is bijective. Therefore no distinction is usually made between multiplicative linear functionals and maximal ideals. The formula a(m) = m(a) (m E M) assigns a function a : M --> C to each a E A. This function is referred to as the Gelfand transform of a. Let A be the set {a : a E A}. The Gelfand topology on M is the coarsest
(weakest) topology on M which makes all functions aE A continuous. The set M equipped with the Gelfand topology is called the maximal ideal space of A. One can show that M is a compact Hausdorff space. The map
f: A--> C(M), a I-t a
is called the Gelfand map of A.
Theorem 2.25 (Gelfand). Let A be a commutative Banach algebra with identity element and let M be the maximal ideal space of A. An element a E A is invertible if and only if a(m) I- 0 for all mE M.
In words: the Gelfand map is a Banach algebra homomorphism of A into C(M) which preserves spectra. It can be shown that f actually has the norm 1, Le., Iiall oo :S Iiall for every a E A. A proof of Theorem 2.25 is in every textbook on Banach algebras.•
Example 2.26: singly generated algebras. A Banach algebra A with identity element e is said to be singly generated by an element c E A if the smallest closed subalgebra of A containing e and c coincides with all of A. One can show that in this case the maximal ideal space of A is homeomorphic to sp c (with the topology induced from the embedding sp c C C) and that the Gelfand map can be given by
f: A --> C(spc), (ff(c))('\) = f('\)
for every polynomial f. •


 2.6 Local Principles 53
Example 2.27: Wiener algebras. It turns out that the multiplicative linear functionals of the Wiener algebra Ware the maps
'PT : W ---. C, a f---> a(r) (r E T).
Thus, the maximal ideal space M(W) of W can be identified with T and the Gelfand map is then nothing but the embedding r : W ---. C(T). Hence, Theorem 2.25 immediately yields Wiener's theorem: a E W is invertible in W if and only if a(r) =1= 0 for all rET. Analogously, the Gelfand maps of W+ and W _ are given by
r: W+ ---. C(D), (r ~ anXn) (z) = ~ anzn,
r: W_ ---. C(D), (r~anx-n)(z)= ~anzn,
where
D := {z E c: Izi :s I}.
Theorem 2.25 therefore implies the invertibility criteria for W± cited in Section 1.5.•
Example 2.28: the simplest Toeplitz algebra. Let A(C) be the smallest closed subalgebra of BW) containing the set {T(a) : a E C}, i.e., all Toeplitz operators with continuous symbols. It is easily seen that every finite-rank operator and thus every compact operator belongs to A(C) (see, e.g., [39, p. 155]). Consequently,
V:= {T(c) + K: c E C,K E .ql2)} C A(C).
Let c E C and K E K(l2). By Theorem 1.17, the spectral radius of T(c) +
K(l2) in the Calkin algebra is Ilcl/ oo . Therefore
Ilclloo ::;dist(T(c),K(l2»)::; IIT (c)+KII, (2.40)
which shows that V is a closed subset of BW). This observation together with Proposition 1.12 and the fact that Hankel operators with continuous symbols are compact shows that in fact V = A(C), i.e.,
A(C) = {T(c) + K : c E C, K E K(l2)}. (2.41 )
Abbreviate the coset T(c) + KW) to T1r(c). From (2.41) we infer that
(2.42)
Denote the Banach algebra (2.42) by A 1r(C). The algebra A 1r(C) is commutative (again by Proposition 1.12 and the compactness of Hankel operators


 54 2. Finite Section Method and Stability
with continuous symbols). Using Theorem 1.17 one can easily verify that the multiplicative linear functionals of A'7r (C) are the maps 'fir : T'" (c) I-> c(T) (T E T). Hence, we can identify the maximal ideal space of A'" (C) with T and can write the Gelfand map as
r: A 7r (C) -> C(T), T"'(c) I-> C.
This map r is readily seen to be even an isometric Banach algebra isomorphism (recall (2.40»). Therefore, we henceforth tacitly identify A"'(C) and C:= C(T) .•
Local principles. Theorem 2.25 associates with every element a of a unital commutative Banach algebra a collection of numbers, {O,( m) }mEM, in terms of which we can decide whether the given element is invertible or not. The idea behind so-called local principles is to associate with an element of a non-commutative unital Banach algebra a set of simpler objects which can answer for invertibility of the given element. One concrete realization of this strategy is the following theorem. The center of a Banach algebra A is the set of all z E A such that za = az for all a E A. Note that the center and every subalgebra of the center are automatically commutative.
Theorem 2.29 (Allan-Douglas). Let A be a Banach algebra with identity element e and let Z be a closed subalgebra of the center of A which contains e. Denote the maximal ideal space of Z by f2, and for each maximal ideal w E f2, let Jw be the smallest closed two-sided ideal of A which contains the set w. Then an element a E A is invertible in A if and only if the coset a + Jw is invertible in AIJw for every w E f2.
A proof of this theorem is in [39, Theorem 1.34]' for example.•
We remark that if Jw = A, then we consider a + Jw as invertible in AI Jw by definition. The algebra AIJw is referred to as the local algebra of A at
w E f2, the spectrum of a + Jw in AIJw is called the local spectrum of a at w E f2, and every element aw E A for which aw + Jw = a + Jw is said to be a local representative of a at w.
If A itself is commutative, we can take Z = A, and since AIJw = Alw is isomorphic to C (Gelfand-Mazur theorem), Theorem 2.29 goes over into Theorem 2.25. Clearly, the larger the center of an algebra A is the finer we can localize in A using Theorem 2.29. In case the center is trivial, i.e., equal to {Ae : A E C}, Theorem 2.29 merely says that a is invertible if and only if a is invertible.
Example 2.30: the local essential range. Let A be the (commutative) Banach algebra L= and put Z = C. The maximal ideal space of Z is T: the maximal ideal associated with T E T is the set {c E C : C(T) = O}. The corresponding ideal Jr C L= is the closure of the set of all finite sums of


 (2.44)
2.6 Local Principles 55
the form
LCjfj with Cj E C, Cj(T) = 0, fj E Loo .
j
One can show that actually
J.r = {cf: C E C, C(T) = 0, f E LOO } (2.43)
(see, e.g., (31, Proposition 8.6]). If a E PC, then obviously a+JT = ar+JT where aT E PC is any function such that aT (T ± 0) = a(T ± 0). This easily implies that the spectrum of
a + Jr is the set {a(T - O),a(T + On. In the general case, a E Loo, it is not difficult to see that the local spectrum of a at T, Le., the spectrum of a + JT, is just the set 'RT(a) introduced in Section 1.7. Moreover, the norm
Iia + JTII is nothing but the number l?T(a) we encountered in Section 1.7.
In the case at hand, Theorem 2.29 simply says that a function a E Loo is invertible in L OO if and only if 0 tj. 'R-r(a) for every T E T .•
Example 2.31: operators of local type. Consider the Calkin algebra /37r := /3(l2)/JC(l2) and write A7r := A+JCW) for A E /3(l2). The operators in
A:= {A E /3(l2) : AT(c) - T(c)A E JC(l2) for all c E C}
are called operators of local type. Clearly, A contains JC(l2), and by virtue of Proposition 1.12 and the compactness of Hankel operators with continuous symbols, every Toeplitz operator T(a) with a E LOO belongs to A. Put A
7r := AIJC(l2). By the definition of A, the algebra C = A 7r (C) of Example 2.28 is contained in the center of A7r. The algebra A7r is obviously inverse closed in /37r: if A E A and A 7r is invertible in /37r, then the inverse of A 7r belongs to A11'. Hence, an operator A E A is Fredholm if and only if A7r is invertible in A1I'. We can therefore employ Theorem 2.29 with A = A7r and Z = C = A 7r (C) to study Fredholmness of operators of local type. The ideal JT C A7r corresponding to T E T = M (C) is the closure of the set of all finite sums
L T7r (cj)Bj with Cj E C, Cj(T) = 0, B j EA.
j
Again it can be shown that in fact
JT = {T7r (c)B 7r : C E C, C(T) = 0, BE A}.
Put A; := A7r + Jr. We so infer from Theorem 2.29 that if A E A, then A
is Fredholm if and only if A; is invertible in A7r I JT for every T E T .•
Theorem 2.32. Let a E LOO. For T E T, put T:(a) := T7r(a) + JT where J
T is given by (2.44). Then
'RT(a) C spT:(a) c conv'RT(a).


 56 2. Finite Section Method and Stability
The right incl usion of this theorem easily follows from the definition of the local essential range R.r (a): if 0 ~ conv R.r (a), then there is a neighborhood U E Ur such that 0 ~ conv R.u(a) (recall Section 1.7), hence the function given by
a t ._ { a(t) for t E U,
u( ) .- >'0 E conv Ru(a) for t E T\U
induces an invertible Toeplitz operator (Theorem 1.18), and since T: (a) = T; (au), it results that T: (a) is invertible. The left inclusion of Theorem 2.32 is less trivial; a proof is in [39, Corollary 3.64] .•
Second proof of Theorem 1.21. If a E Loo is locally sectorial on T, then 0 ~ convRr(a) for every T E T. Hence, by Theorem 2.32, T:(a) is invertible for every T E T. From Theorem 2.29 and Example 2.31 we therefore deduce that T( a) is Fredholm.•
Notes. The reasoning of Example 2.27 goes back to LM. Gelfand and was one of the first triumphs of the theory of Banach algebras. The results of Example 2.28 are due to Gohberg [79] and Coburn [50]. Theorem 2.29 was established by Allan [1]. In the case of C*-algebras, Theorem 2.29 was independently discovered by Douglas [59, Theorem 7.47], who was also the first to realize the relevancy of this theorem in operator theory. Operators of local type were introduced by Simonenko [160]. He also developed a local principle for their investigation. This local principle was subsequently essentially simplified and generalized by Gohberg and Krupnik [87] and Kozak [109]. These local principles are all more or less equivalent to Theorem 2.29. Local Toeplitz operators, i.e., the cosets T:(a), are an invention
of Douglas [60]. Douglas also asked whether sp T: (a) is a connected set for every a E Loo. This problem is still open. That the ideal Jr is of the form (2.43), (2.44) was probably first observed by Semenyuta and Khevelev [150].
2.7 Localization of Stability
We now apply Theorem 2.29 to the algebra S /.:J. Our first objective is to obtain a finite section analogue of Example 2.28. Let S(C) denote the smallest closed subalgebra of S (or F) containing the set {{Tn(c)} : c E C}.
Proposition 2.33. The algebra S(C) coincides with the set
Proof. The set under consideration is a closed subalgebra of S (recall the proofs of Lemma 2.21 and Theorem 2.23 and take into account (2.40)).


 2.7 Localization of Stability 57
One can also show that this set is contained in 8(C) (see [39, Proposition 7.27]). This implies the assertion.•
From Example 2.28 and Proposition 2.33 we see that .:J is a closed twosided ideal of 8(C). Put
8 1r (C) = 8(C)I.:J·
By Proposition 2.33, 8 1r (C) = {{Tn(c)}1r : C E C}. Proposition 2.12 and the fact that Hankel operators with continuous symbols are compact show
that 8 1r (C) is commutative.
Proposition 2.34. The maximal ideal space of 8 1r (C) can be identified with T and the Gelfand map is given by
r: 8 1r (C) --t C(T), {Tn(c) r f-4 c.
Proof. The map <P: 8(C) -t A1r(C), {An} f-4 (s-limn--+oo An )1r is a surjective Banach algebra homomorphism. From Proposition 2.33 we infer that
Ker <P = .:J. This shows that 8 1r (C) is isomorphic to A1r (C). Example 2.28 completes the proof. •
We henceforth freely identify S1r(C) and C. In analogy to operators of local type, we define ~ as the set of all {An} E S satisfying {AnTn(c) - Tn(c)An } E .:J for all c E C. By Proposition 2.12 and (the sufficiency part of) Theorem 1.16, ~ contains {Tn (a)} for every a E L00. Let ~1r := ~ I.:J. Then C = S1r (C) is contained in the center of ~1r. Obviously, if {An} E ~ and {AnY is invertible in SI.:J, then {AnY is also invertible in ~1r = ~/.:J. For T E T, let Jr be the smallest closed two-sided ideal of ~1r containing {{Tn(c)}1r : c E C, C(T) = O}. One can show that
Jr = {{Tn(c)Bn }1r : c E C, C(T) = 0, {Bn } E ~}.
Denote by {An}; the coset {An Y + J r in the local algebra ~1r1Jr'
Theorem 2.35. Let {An} E ~. Then {An }1r is invertible in SI.:J if and only if {An}; is invertible in ~1r!Jr for every T E T.
Proof. Immediate from Theorem 2.29 and the above discussion.•
Theorem 2.36. If a E Loo , then for every T E T,
The right inclusion can be verified as the corresponding inclusion of Theorem 2.32 (also recall Proposition 2.17), the left inclusion follows from [39, Corollary 3.64] .•


 58 2. Finite Section Method and Stability
Second proof of Theorem 2.18. If a E Loo is locally sectorial on T, then {Tn (a)}; is invertible for every T E T by virtue of the right inclusion of Theorem 2.36, and hence {Tn (a)}1r is invertible in SI.:! due to Theorem 2.35. If, in addition, T(a) is invertible, it results from Corollary 2.24 that {Tn (a)} is stable.•
Note. In this section we followed [154] and [36].


 3
Narms of Inverses and Pseudospectra
3.1 C*-Algebras
C*-algebras are especially nice Banach algebras. A map a 1---+ a* of a Banach algebra A onto itself is called an involution if
a** = a, (a+b)*=a*+b*, (ab)* = b*a*, (>.a)* = Xa*
for all a, b E A and all >. E C. A C*-algebra is a Banach algebra with an involution such that
Ilaa* II = IIal1 2 for all a E A. (3.1)
Examples. If X is a Hausdorff space, then C(X) is a C*-algebra. The algebra Loo as well as their subalgebras C and PC are C*-algebras. In these cases the involution is given by complex conjugation, a f-+ a. Although complex conjugation is an involution on the Wiener algebra W, it does not make W into a C*-algebra: if a(t) = _C l + 1 + t (t E T),
then (aa)(t) = -C 2 + 3 - t 2 , whence Ilaallw = 5 and Ilall~ = 9.
If H is a Hilbert space, then the algebras B(H) and K(H) of all bounded and compact linear operators on Hare C*-algebras with passage to the adjoint operator as the involution. The involution {An }* ;= {A~} makes the algebras F and S introduced in Section 2.5 into C*-algebras. A subset of a C*-algebra is said to be selfadjoint if it is invariant under the involution. Clearly, every closed and selfadjoint subalgebra of a C*-algebra is itself a C*-algebra. The algebra Fe of all sequences {An} E F which have a strong limit is not a selfadjoint subalgebra of F (recall the example before


 60 3. Norms of Inverses and Pseudospectra
Proposition 2.3: there An ----+ 0 while A~ does not at all converge strongly). However, the algebra Fcc of all sequences {An} E F for which there exists an operator A E l3(l2) such that An ----+ A and A~ ----+ A (strongly) is a C*-subalgebra of the C*-algebra F. If A is a C*-algebra and J is a closed two-sided ideal of A, then J is automatically selfadjoint and AIJ provided with the involution (a+J)* := a* + J and the usual quotient norm is a C*-algebra. In particular, FIN
and S I J are C*-algebras. The algebras A(C), A"(C) (Section 2.6) and S(C), S1l"(C) (Section 2.7) are also C*-algebras with natural involutions.
Inverse closedness. If A is a Banach algebra with identity and 13 is a closed subalgebra of A which contains the identity, then for an element b E l3 the spectrum in l3 may be larger than its spectrum in A (example: SPu",Xl = T, sPHooXl = D). As the following well-known result shows, this cannot happen for C*-algebras.
Proposition 3.1. If A is a C*-algebra with identity and l3 is a C*-subalgebra of A which contains the identity, then for every b E l3 the equality
sP13 b = SPA b
holds. Shortly: unital C*-algebras are always inverse closed.
Homomorphisms and isomorphisms. A map <p : A ----+ l3 of a C*-algebra A to a C*-algebra l3 is referred to as a C*-algebra homomorphism if <p is a Banach algebra homomorphism and <p(a)* = <p(a*) for all a E A. Bijective C*-algebra homomorphisms are called C*-algebra isomorphisms. One can show that if <p : A ----+ l3 is a C*-algebra homomorphism, then <p(A) is a C*-subalgebra of l3 (which includes that <p(A) is always a closed subset of l3). A C*-algebra homomorphism <p : A ----+ l3 of unital C*-algebras A and l3 is said to preserve spectra if
sp<p(a) = spa for every a E A
and is referred to as an isometry if
11<p(a)11 = Iiall for every a E A.
The following simple result will prove to be very useful in what follows.
Proposition 3.2. Let A and l3 be two C*-algebras with identities and let <p : A ----+ l3 be a C*-algebra homomorphism.
(a) If <p preserves spectra, then <p also preserves norms, i.e., <p is an isometry.
(b) If <p is injective, then <p preserves spectra.


 3.2 Continuous Symbols 61
Proof. (a) Let a E A. Since both aa* and ep(a)ep(a)* are selfadjoint and the norm of a selfadjoint element of a C*-algebra coincides with its spectral radius, we obtain from (3.1) that
IIal1 2 Ilaa*11 = max{I..\1 :..\ E sp(aa*)} max{I..\I:..\ E spep(aa*)}
max{I..\1 : ..\ E sp(ep(a)ep(a)*)}
lIep(a)ep(a)*11 = lIep(a)11 2 .
(b) Clearly, sp ep(a) C sp a for every a E A. Conversely, suppose ep(a- ..\e) is invertible. Since ep(a - ..\e) lies in ep(A) and ep(A) is a C*-subalgebra of 5, it follows from Proposition 3.1 that the inverse of ep(a - ..\e) belongs to ep(A) and is therefore of the form ep(c) with c E A. Then injectivity of ep implies that c is the inverse of a - ..\e.•
For C*-algebras, Theorems 2.25 and 2.29 can be strengthened.
Theorem 3.3 (Gelfand-Naimark). If A is a commutative C*-algebra with identity element then the Gelfand map r : A ---+ C(M) is an isometric C*-algebra isomorphism of A onto C(M).
Theorem 3.4 (Allan-Douglas). Let the situation be as in Theorem 2.29. In addition, suppose A is a C*-algebra and Z is a C*-subalgebra of A. Then for every a E A,
IIall = max Iia + Jwll
wEn
and the maximum is attained for some Wo En.
One can show that under the hypothesis of Theorem 3.4 we have Jw i=- A for all wEn. For proofs of Theorems 3.3 and 3.4 we refer to [59, Theorems 4.29 and 7.49] and [39, Theorem 1.34].•
3.2 Continuous Symbols
Let a E C and suppose T(a) is invertible. Then {Tn(a)} is stable (Theorem 2.11), hence T;l(a) ---+ T-1(a) strongly (Propositions 2.2 and 2.4), and thus (3.2)
by the Banach-Steinhaus theorem (Theorem 2.1). The stability of {Tn (a)} is equivalent to the estimate
lim sup liT; 1(a)1I < 00.
n~oo


 62 3. Norms of Inverses and Pseudospectra
The purpose of this section is to show the stronger inequality
lim sup IIT;l(a)1I :S IIT-l(a)ll·
n-+CXJ
Obviously, (3.2) and (3.3) imply that
lim IIT;l(a)11 = IIT-l(a)ll.
n-+CXJ
(3.3)
(3.4)
C*-algebras in action. To prove (3.3), we will employ Proposition 3.2 and are thus led to the study of C*-algebras generated by sequences of Toeplitz matrices. Consider the algebra S(C), whose structure is described by Proposition 2.33. The direct sum BW) ED BW) is a C*-algebra with componentwise algebraic operations and the norm
II(A,B)II := max{IIAII, II B II}·
Define (3.5)
where
Notice that if
A := s-lim An,
n-+CXJ A := s-lim WnAnWn.
n-+CXJ
(3.6)
with K, L E KW) and {Cn} EN, then the two operators (3.6) are
(3.7)
A=T(a)+K, A=T(a)+L. (3.8)
From (3.6) it is clear that 'P is a C*-algebra homomorphism. Taking into account (2.40) we see that the two operators A and A are zero if and only if a = 0 and K = L = O. Hence, Ker'P = N. This shows that the map
is a well-defined and injective C*-algebra homomorphism. The Sym stands for "symbol". We now let Proposition 3.2 do its job.
Theorem 3.5. A sequence {An} E S(C) is stable if and only if the two operators A and A are invertible.
Proof By Propositions 2.20 and 3.1, the stability of {An} is equivalent to the invertibility of {An}+N in S(C)jN. As Sym is an injective C*-algebra homomorphism, we deduce from Proposition 3.2(b) that {An} + N is invertible if and only if so are A and A. •


 3.2 Continuous Symbols 63
Theorem 3.6. If {An} E 8(C), then
lim IIAnll = max{IIAII, IIAII}.
n-+oo (3.9)
Proof Since Sym is injective, we can use Proposition 3.2 to conclude that
lim sup IIAnl1 = II{An} +NII = max{IIAII, IIAII}· (3.10)
n-oo Because
IIAII ~ liminfllAnll, IIAII ~ liminfllWnAnWnl1 = liminfllAnll
n-+oo n-+<x> n--+<x>
by Theorem 2.1, we arrive at (3.9).•
To be a little more explicit, we note that (3.7), (3.8), (3.9) give
whenever a E C, K E K(l2), L E K(l2).
Theorem 3.6 will imply the desired equality (3.4). We first mention the following result for sequences {An} E Fcc (recall Section 3.1). Notice that we put IIR-111 = 00 in case R is a non-invertible operator.
Proposition 3.7. If {An} E Fcc and the strong limit of An is not invertible, then
lim IIA~lll = 00.
n-oo
Proof Since {An} E Fcc, we have an operator A E B(l2) such that An ---> A and A~ ---> A* strongly. Assume there are nl < n2 < ... and M < 00 such that IIA;;-;II ::; M. Then for every x E l2,
and letting nk ---> 00 we get
Ilxll ::; MIIAxll, Ilxll ~ MIIA*xll.
which is impossible if A is not invertible.•
Corollary 3.8. If a E C and K E K(l2), then
Proof If T(a) + K is not invertible, the assertion follows from Proposition 3.7. So suppose T(a) + K is invertible. Then T(a) and thus also T(ii) are


 64 3. Norms of Inverses and Pseudospectra
Fredholm of index zero and therefore invertible (Theorem 1.10 or Theorem 1.17). Let An := Tn(a) + PnKPn. The two limits (3.6) are A = T(a) + K
and A = T(a). By Theorem 3.5, {An} is stable. Hence, by Propositions
2.20 and 3.1, {An} + N is invertible in S(C)/N, i.e., there is a sequence {Bn } E S(C) such that
(3.12)
Denote the strong limits of B n and WnBnWn by Band H, respectively.
From (3.12) we get AB = BA = I and AH = HA = I, whence B = A-I
and H = A-I. Theorem 3.6 gives
and because, again by (3.12), limn-+ oo IIA~lll = limn-+oo IIBnll, we arrive at the assertion.•
Corollary 3.9. If a E C, then
First proof. This follows from Corollary 3.8 for K = 0 along with the fact
that T(a) is the transposed operator ofT(a), by virtue of which IIT- I (a)11 = IIT-I(a)ll· •
Second proof. If T(a) is not invertible, we can make use of Proposition 3.7. In the case where T(a) is invertible, Theorem 2.14 gives
T;I(a) = Tn(a- I ) + PnK(a)Pn + WnK(a)Wn + Cn
with K(a), K(a) E KW) and IICnl1 ---> O. Consequently, by (3.11),
max {IIT(a- 1) + K(a)ll, IIT(a- l ) + K(a)ll}
max {IIT-l(a)ll, IIT-1(a)ll} = IIT-I(a)II .•
Note. The method and the results of this section are from [155] and [23].
3.3 Piecewise Continuous Symbols
In this section we extend Theorems 3.5 and 3.6 to sequences {An} in the smallest closed subalgebra S(PC) of S (or F) containing {{Tn (a)} : a E PC}. Let A(PC) stand for the closed subalgebra of B(12) generated by the operators T(a) with a E PC. Put
A"(PC) := A(PC)/K(12), S"(PC) := S(PC)/J


 3.3 Piecewise Continuous Symbols 65
(note that K.(12) c A(PC) by Example 2.28 and .:J c S(PC) due to Proposition 2.33).
Theorem 3.10. The algebras A"" (PC) and S"" (PC) are commutative C*algebras, their maximal ideal spaces can be identified with the cylinder T x [0,1] (with an exotic topology, see Figure 15), and the Gelfand maps are for a E PC given by
(rT""(a))(t,/.1)
(r{Tn(a) }"")(t, /.1)
where t E T and /.1 E [0,1].
(1 - /.1) a(t - 0) + /.1a(t + 0),
(1 - /.1) a(t - 0) + /.1a(t + 0),
1.5 ,---,-----.----------.---,
-0.5 L-------'- -'--_ _-'------l
0.5
o
Fig. 15a----
I
-I 0
1.5 Fig. 15b
"--
0.5
0
-0.5 -I 0
Neighborhood bases of a point (t, /.1) E T x [0,1] are formed by sets as in Figure 15a (/.1 E (0,1)) and Figure 15b (/.1 = 1).
Proof To show that A""(PC) is commutative, we have to check whether T7r(a)T""(b) = T7r(b)T""(a) whenever a,b E PC. Obviously, it suffices to consider the case where a and b have only one jump, at Q and /3, say. Suppose first that Q I=- /3. There are functions cp, 'l/J E C such that
cp2 + 'l/J2 = 1, cp(Q) = 1, cp(/3) = 0, 'l/J(Q) = 0, 'l/J(/3) = 1.
We have
By Proposition 1.12,
T"" (acp2b) - T"" (a)T7r (<p2)T"" (b)
= T 7r (acpcpb) - T""(acp)T7r (cpb) = H""(acp)H7r (cj5b),


 66 3. Norms of Inverses and Pseudospectra
and since 'Pb is continuous, H7f (<pb) = O. Analogously one can show that
This implies that (3.13) is compact and proves that T7f(a) and T7f(b) commute. If Q = (3, there is a constant>' E C and a function c E C such that
a = )"b + c. It follows that
T(a)T(b) - T(b)T(a) T(>'b + c)T(b) - T(b)T(>'b + c)
T(c)T(b) - T(b)T(c),
and as c is continuous, the latter commutator is compact. This completes the proof of the commutativity of A 7f (PC).
Let f : A 7f (PC) -t C be a multiplicative linear functional. Then the restriction of f to A 7f (C) is a multiplicative linear functional on A 7f (C) and hence, by Example 2.28,
with some T E T. Let Xr E PC be the characteristic function of the half
circle {Tei8 : 0 < () < 1r} and put
Then J-L E spT7f (Xr) = sPessT(Xr) = [0,1] by Theorems 1.23 and 2.25. As every a E PC can be written in the form
a = a(t - 0)(1 - Xr) + a(t + O)xr + c,
where c E PC is continuous at T and C(T) = 0, it follows that
f(T7f (a») = a(t - 0)(1 - J-L) + a(t + O)J-L. (3.14)
We have shown that every multiplicative linear functional f : A 7f (PC) -t C acts on elements of the form T7f(a) (a E PC) by the formula (3.14) with some (t, J-L) E T x [0,11. From Theorems 1.23 and 2.25 we see that for every (t, J-L) E T x [0,1] there must exist a linear multiplicative functional f such that (3.14) holds. At this point we have proved all assertions concerning A 7f (PC). The commutativity of S7f (PC) can be shown as the commutativity of A 7f(PC) (simply use Proposition 2.12 instead of Proposition 1.12). If f is a multiplicative linear functional on S7f(PC), then there is aTE T such that
f( {Tn(c)} 7f) = C(T) for all c E C
by virtue of Proposition 2.34. Let Xr be as above and put


 3.3 Piecewise Continuous Symbols 67
Again It E sP{Tn(XT)P, and since {Tn(XT - A)} is stable and therefore {Tn(XT) - APn}7T is invertible whenever A rj. [0,1] (Proposition 2.17), it follows that It E [0, 1]. Consequently, if a E PC, then
f( {Tn(a)} 7T) = a(t - 0)(1 -It) + a(t + 0)1t. (3.15)
Finally, since T(a - A) is Fredholm if {Tn(a - A)}7T is invertible (just pass to the strong limit n -. 00), it follows that for every (t,lt) E T x [0,1] there is a multiplicative linear functional f for which (3.15) is valid.•
In analogy to (3.5), consider the map
where A and A are given by (3.6). As S(PC) is of much more intricate structure than S(C), the simple injectivity argument used in Section 3.2 does not work in the present case. However, it is obvious that N c Ker <p, hence
is a well-defined C*-algebra homomorphism, and we will show that Sym is isometric by proving that Sym preserves spectra.
Theorem 3.11. A sequence {An} E S(PC) is stable if and only if both A and A are invertible.
Proof. By Theorem 2.23, {An} is stable if and only if A and A are invertible and {An} 7T is invertible in S j :J. We will prove that the invertibility of
{An V in S j:J is equivalent to the Fredholmness of A. This clearly gives the assertion.
By Proposition 3.1, {An V is invertible in S j:J if and only if {An} 7T is invertible in S7T(PC) = S(PC)j:J. Combining Theorems 3.3 and 3.10 we see that this is equivalent to the invertibility of A7T in A7T (PC) = A(PC)jKW), which, again by Proposition 3.1, is equivalent to the invertibility in BW)jK(l2) and thus to the property of being Fredholm.•
Theorem 3.12. If {An} E S(PC) then
lim IIAnl1 = max {IIAII, IIAII}·
n--+oo
Proof. Since {An} E S(PC) is stable if and only if {An} +N is invertible in S(PC)jN (Propositions 2.20 and 3.1), Theorem 3.11 says that Sym preserves spectra. Proposition 3.2(a) therefore gives (3.10), and the rest is as in the proof of Theorem 3.6.•
Here are a few concrete examples.


 68 3. Norms of Inverses and Pseudospectra
Corollary 3.13. (a) Let ajk be a finite collection of functions in PC and put
An = I:IITn(ajk),
jk
Then
A = I:IIT(ajk),
jk
A = I:IIT(ajk)'
jk
lim IIA~III = max{IIA-111, IIA-III}.
n--+<XJ
(b) If a E PC and K E K.(l2), then
nl~~ II (Tn (a) + PnKpn)-111 = max{II(T(a) + K)-II/, IIT-I(ii)II}·
(c) If a E PC, then
(3.16)
Proof (a) If both A and A are invertible, the assertion follows as in the proof of Corollary 3.8. In case A is not invertible, we deduce from Proposition 3.7 that II A;;: III ----> 00. Finally, if A is not invertible, we obtain analogously
that II A;;: I II ----> 00 where An := WnAnWn. Since
it results that IIA;;:III----> 00.
(b) Proceed as in the proof of Corollary 3.8.
(c) Since T(ii) is the transposed operator of T(a), this follows immediately from part (b) .•
Locally normal symbols. We do not know how to prove equality (3.16) under the sole assumption that a be locally sectorial on T. However, Theorems 3.11, 3.12 and Corollary 3.13 remain valid for so-called locally normal symbols. As first observed by Brown and Halmos [43], a Toeplitz operator T(a)
(a E LOO ) is normal, i.e., T(a)T(a) = T(a)T(a), if and only if convR(a) is a line segment. We therefore call a function a E LOO locally normal on T if conv R T (a) is a line segment for every T E T (of course, this line segment may change with T E T). Obviously, functions in PC or functions for which R
T (a) consists of at most two points for every T E T are locally normal. Given a locally normal function a E L<XJ, we define A(a, a, C) and S(a, a, C) as the smallest closed subalgebra of l3W) and :F which contains
{T(b) : b E {a, a} U C} and {{Tn (b) } : b E {a, a} U C},
respectively, and consider the quotient algebras
A 7T (a,a,C):= A(a,a,C)/K.(l2), S7T(a,a,C):= S(a,a,C)/J.


 3.4 Norm of the Resolvent 69
One can show that these two algebras are commutative C*-algebras. Each of them contains a copy of C (Example 2.28 and Proposition 2.33). We can therefore localize over the points T E T. In analogy to Theorem 3.10, we obtain that the local algebras
are both isomorphic to the C*-algebra C(conv'R-r(a)). Using this, we can show that Theorems 3.11 and 3.12 as well as Corollary 3.13(a) remain literally true with PC replaced by {a, a} U C, where a is a (fixed but arbitrary) function, and that parts (b) and (c) of Corollary 3.13 hold for every locally normal function.
Notes. For A 1r(PC), Theorem 3.10 is Gohberg and Krupnik's [88]. The part of Theorem 3.10 concerning S1r(PC) was established in our paper [36]. The latter paper is probably the first work in which C*-algebra techniques were employed in the context of a concrete problem of numerical analysis. The proof of Theorem 3.10 given here is essentially from [35, pp. 35-38]. All other results of this section are taken from our papers [155] and [23].
3.4 Norm of the Resolvent
We will use the results of the previous two sections in order to determine the limiting sets of the pseudospectra of Toeplitz matrices. This will be done in the following section, and the theorem of the present section will be a main ingredient of the proof. It is well known that nonconstant complex-valued analytic functions cannot have locally constant modulus. This is no longer true for operatorvalued analytic functions: for example, if
then IIA(>')II = max{I>'I, I}, which is constant on the unit disk. The following theorem shows that such a phenomenon does not occur for the resolvent. We learned both this theorem and its proof from Andrzej Daniluk of Cracow (private communication; see [23] and [41]).
Theorem 3.14. Let H be a Hilbert space and let A E B(H). Suppose that A - >"1 is invertible for all >. in some open subset U of C and assume that II(A - >'1)-111 S; M for all >. E U. Then II(A - >'1)-111 < M for all >. E U.
Proof. A little thought reveals that what we must show is the following: if
U is an open subset of C containing the origin and II (A - >'1) -111 S; M for all >. E U, then IIA-111 < M. To prove this, assume the contrary, Le., let


 70 3. Norms of Inverses and Pseudospectra
IIA-III = M. We have
00
(A - >'1)-1 = L >.i A-i- l
i=O
for all >. in some sufficiently small disk 1>'1 ~ r. Given x E H, we therefore get
II(A - >'I)- I x I12 = L >.iXk(A-i- I X , A-k-Ix)
i,k?O
whenever 1>'1 ~ r. Integrating the latter equality along the circle 1>'1 = r, we obtain
and since II(A - reiO I)-lxll ~ M IIxll, we arrive at the inequality
Now pick an arbitrary E > O. Because IIA-III = M, there is an Xc E H such that Ilxcll = 1 and IIA-I xc I12 > M 2 - E. It follows that
M 2 _ E + r 2 11A-2 x e 11 2 < M 2 ,
Le., IIA-2 xe 112 < c.r- 2, and consequently,
which is impossible if E > 0 is small enough.•
3.5 Limits of Pseudospectra
As will be seen in Chapter 5, the spectrum spTn(a) need not mimic spT(a) as n goes to infinity (also recall Figure 13). In contrast to this, pseudospectra behave as nicely as we could ever expect.
Pseudospectra. For E > 0, the E-pseudospectrum sPeA of a bounded linear Banach space operator A is defined as the set
sPcA := {>. E C : II(A - >'1)-111 ~ lie}. (3.17)
Here we put II(A->'1)- 1 1l = 00 if A->.I is not invertible. Thus, sp A C sPeA for every e > O. In the same way the question "Is A invertible?" is in numerical analysis
better replaced by the question "What is IIA- I II?", the pseudospectra of


 (3.18)
3.5 Limits of Pseudospectra 71
matrices and operators are, in a sense, of even greater import than their usual spectra. The following theorem provides an alternative description of pseudospectra.
Theorem 3.15. Let H be a Hilbert space and let A E l3(H). Then for every c: > 0,
sPe A = U sp(A + E), IIEII:S:e
the union over all E E l3(H) of norm at most c:.
Proof. Let 8 1 and 82 be the sets on the right of (3.17) and (3.18), respectively. To prove that 82 C 81, let A E 82 and choose an E E B(H) such that
II Ell::; c: and A + E - AI is not invertible. If A E sp A, then clearly A E 81 . So assume A - AI is invertible. From the identities
A+E-AI = (A-A1)(I+(A-AI)-lE)
= (I + (A - A1) -1 E) (A - AI)
we see that I + (A - A1)-l E cannot be invertible. Hence
and, consequently,
which shows that A E 8 1, We now prove that 8 1 C 82 , Contrary to what we want, let us assume
that there is a A E 81\82 . Then A + E - AI is invertible whenever IIEII ::; c:. Letting E = 0, we obtain that A - AI and thus also A * - >'1 is invertible.
Choosing E = J.L( A * - >'1) - 1 with an arbitrary J.L E C satisfying
°
< IJ.LI ::; c:/II(A* - >'1)-111
we arrive at the conclusion that
A - AI + J.LE A - AI + J.L(A* - >'1)-1
= J.L(A - A1)(J.L- 1I + (A - AI)-l(A* - >'1)-1)
is invertible. Thus,
(3.19)
is invertible for all J.L subject to (3.19), which implies that the spectral radius
of (A - AI)-l(A* - >'1)-1 is less than II(A* - >'I)- 111/c:. As the operator (A - A1)-l(A* - >'I)-1 is selfadjoint, it results that
II(A - AI)-l(A* - >'1)-111 < II(A* - >'1)-1 II/c:.


 72 3. Norms of Inverses and Pseudospectra
Hence (recall (3.1))
II(A - A1)-111 2 < II(A* - "XI)-II1/c = II(A - A1)-II1/e:
and thus II(A - A1)-111 < lie:. This contradicts our assumption that A be in SI .•
Example 3.16. The previous theorem can be used to get a good idea of the c-pseudospectrum of a matrix A. Namely, we can randomly perturb A by matrices E satisfying IIEII ~ c and look at the superposition of the plots
of the spectra (= eigenvalues) of A + E. For example, consider the symbol
a(t) = _t4 - (3 + 2i)C3 + it2 + t- 1 + lOt + (3 + i)t2 + 4t3 + it4 ,
where t E T. The range a(T) (a "fish", or better, a "whale") and the eigenvalues of TlOo(a) are plotted in Figure 16, while Figure 17 shows the
superposition of the (usual) spectra of T50 (a) + E for 50 randomly chosen
matrices E subject to the constraint IIEII = 10-2 . And what do we see on the screen of the computer when numerically computing the eigenvalues ofTn(a) for large n? Using matlab, we computed the eigenvalues ofTn(a) for n = 200, n = 400, n = 500, n = 700. The results are shown in Figures 18, 19, 20, and 21. Thus, if we blindly trusted in the computer, we could arrive at the conclusion that the eigenvalues of Tn (a) eventually mimic the range of a(T), i.e., sPess T(a). In Chapter 5 we will show that this guess is wrong! In Figure 22 we see the eigenvalues of Tn (a) for n = 300 as they appear on the computer's screen. As already said, this picture is wrong. Clearly, this picture is the result of rounding errors. However, as the result of rounding errors we would rather expect a picture like Figure 23. So why do the rounding errors produce an eigenvalue distribution which, apart from a few outliers, mimics the essential range? A partial answer to this question will be given by Corollary 3.18, which tells us that the pseudospectra of Tn(a) converge to the pseudospectrum of T(a) as n --+ 00.•
Limiting sets. Let MI , M 2 , ... be a sequence of nonempty subsets of C. The uniform limiting set of these sets,
(3.20)
is defined as the set of all A E C which are limits of some sequence {An} with .An E M n . In other words, A belongs to the set (3.20) if and only if there are An E M n such that .An --+ A. We let
p-lim Mn
n-.oo (3.21)
stand for the set of all A E C which are partial limits of some sequence {An} with An E M n , and we refer to (3.21) as the partial limiting set of the sets Mn .


 3.5 Limits of Pseudospectra 73
20
Fig. 16
15 :·f
10 .·····
5 ...
0.
-5
-10
-15
o 5 10 15 20
and the (actual) 100 eigenvalues of the
-20 '-----'-----'---'-----'----'----'-----' -15 -10 -5
The essential range R(a) matrix TlOO(a).
20,-----,.---.----,.------,.----,---,.--------,
15
10
5
o
-5
-10
-15
Fig. 17 o:
o
••••
"000 ~.#"'''
••• s
o :~••••••·0
-20 '-----'-----'---'-----'----'----'-----'
-15 -10 -5 0 5 10 15 20
The superposition of the eigenvalues of 50 matrices Tso(a) + E with
randomly chosen matrices E for which IIEII = 10-2 .


 74 3. Norms of Inverses and Pseudospectra
20,-----,.------.---,---.---------,r-------,----,
15
10
5
o
-5
-10
-15
Fig. 18
.'jiJ
•• * '"
>--_..."'..... .'..-......\
-20 L - _ - - ' -_ _---'----_ _' - - _ - - ' -_ _---'----_ _'--_---l
-15 -10 -5 0 5 10 15 20
The (erroneous) 200 eigenvalues of the matrix T200 (a) as they appear on the computer's screen.
20.------,---.,-----,-----,---,--,--------,
Fig. 19 15
10
5
o
-5
-10
-15
.............'.'.'.'.'.'.
-20 l - _ - - ' -_ _L . . - _ - ' - _ - - - - '_ _-'-_----'-_---.--J
-15 -10 -5 0 5 10 15 20
The (erroneous) 400 eigenvalues of the matrix T400 (a) as they appear on the computer's screen.


 3.5 Limits of Pseudospectra 75
20~-~--~--~--~--.---~--~
Fig. 20 15
10
5
o
-5
-10
-15
-20 L-_---'-_ _-L-_ _.l....-_---'-_ _-L-_ _.l....-_--.I
-15 -10 -5 0 5 10 15 20
The (erroneous) 500 eigenvalues of the matrix T500 (a) as they appear on the computer's screen.
20
Fig. 21 15
10
5
0
-5
-10
-15
-20L-------'-------'------'--------'-------'------'-----.J -15 -10 -5 0 5 10 15 20
The (erroneous) 700 eigenvalues of the matrix T700 (a) as they appear on the computer's screen.


 76 3. Norms of Inverses and Pseudospectra
20,------.--,------,---.-------,---..,------,
15
10
5
o
-5
-10
-15
Fig. 22
1
../ :*
**
.. *
** •
** •
** •
•* •
•* *
.* *
~-_..... .
... ...
"' ... *. '" *.
*. .
*. *
**
"*. *.
•*
**. *.
•*
"'. *",
'*.. *~
o 5 10 15 20
screen as the result of rounding errors
-20 '------'----'----'-----'----'--------''------' -15 -10 -5
This is what we see on the (n = 300).
20,...-----,-----,----.----.-------,----,----,
Fig. 23 15
10
*
5
o
-5
-10
-15 * *
**
*
20
10 15
-5 o 5
-10
-20 '--------'----'---------'-----"--------'----'------' -15
This is what we would expect on the screen as the result of rounding errors.


 3.5 Limits of Pseudospectra 77
Equivalently, A is in the set (3.21) if and only if there are nl < n2 < ... and Ank E Mnk such that Ank ---t A. Clearly, we always have
u-lim Mn C p-lim Mn .
n~CX) n~oo
If Mn = {I} for odd nand Mn = {1,2} for even n, then u-limMn equals {I} while p-limMn is the doubleton {1,2}. In case all the sets Mn are
contained in some disk {A E C : IAI ::; R}, the partial limiting set p-lim M n is never empty; however, u-limMn may be empty in this case (example: M n = {I} for odd nand M n = {2} for even n).
Here is the result of this section.
Theorem 3.17. If {An} E S(PC) and
An ---t A strongly,
then for each E: > 0,
u-lim sp" An = p-lim sp" An = sp" A u sp" A.
n-+oo n-+oo
Proof We first show that sp" A C u-lim sp" An. If A E sp A, then II (An 
AI) -111 ---t 00 by virtue of Proposition 3.7, which implies that A belongs to
u-lim sp"An. So suppose A E sp"A\spA. Then II(A - AI)- l l1 ;:::: lie. Let U E C be any open neighborhood of A. From Theorem 3.14 we deduce that there is a point /-L E U such that II(A - /-LI)- 1 11 > lie. Hence, we can find a ko such that
As U was arbitrary, it follows that there exists a sequence AI, A2, ... such that Ak E SP,,-I/k A and Ak ---t A. By Theorem 3.12,
Consequently, II (An - AkI) -111 ;:::: lie and thus Ak ESP" An for all n ;:::: n(k). This shows that A = lim Ak belongs to u-lim sp" An. Repeating the above reasoning with WnAnWn and A in place of An and A, respectively, we obtain
sp" A C u-lim sp" WnAnWn .
n-+co
Because Wn is an isometry and W~ = I, we have sp" WnAnWn = sp"An . In summary, we have proved that
sp" AU sp" A C u-lim sp" An.
n-+co


 78 3. Norms of Inverses and Pseudospectra
In order to prove the inclusion
suppose A f/. sPe: A U sPe: A. Then II(A - AI)-III and II(A - AI)-III are less than lie, whence
II (An - AI)-111 < 1Ie - 0 < 1lefor all n ~ no
with some 0> °due to Theorem 3.12. Un ~ no and IJL-AI < eO(l/e-o)-I
then
<
1-IJL - AIII(An - AI)-III lie - 0 1 - eo(l/e - o)-I(l/e - 0)
e1 ,
and thus JL f/. sPe: An· This shows that A cannot belong to p-lim sP€ An· •
The following corollary is immediate from Theorem 3.17. For brevity, we put here
lim = u-lim = p-lim .
n-4(X) n-+oc> n-+oo
Corollary 3.18. (a) If ajk is a finite collection of functions in PC, then for each e > 0,
nl~~ sPe: LIT Tn(ajk) = SPe: L LT(ajk) U SPe: LIT T(iijk). jk j k jk
(b) If a E PC and K E KW), then for each e > 0,
lim sPe:(Tn(a) + PnKPn ) = spe:(T(a) + K) U sPe: T(ii).
n-+oo
(c) If a E PC, then for each E > 0,
lim sP€ Tn(a) = sPe: T(a) .•
n-+oo (3.22)
Once again Example 3.16. Comparing Figures 17 and 22 we arrive at the conclusion that the erroneous eigenvalues of Tn(a) we see on the computer's screen are something like the pseudospectrum sPe: Tn(a), with clear preference of points close to the boundary of sPe: Tn(a). Corollary 3.l8(c) says that the limiting set of sPe: Tn (a) is sPe: T(a) and hence, the erroneous eigenvalues must be asymptotically distributed close to the boundary of SP€ T(a). In the case at hand, the boundary of sPe: T(a) is a curve close to a(T) = R(a), which indicates that the erroneous eigenvalues approach a(T) as n goes to infinity. This is at least a rough explanation of the phenomenon we observe in Figures 18 to 21.


 3.5 Limits of Pseudospectra 79
We remark, however, that the argument of the preceding paragraph does neither show why the erroneous eigenvalues are located near the boundary of SPe: Tn(a) nor why they almost exactly approach a(T) (note that the boundary of sPe: T(a) is a curve lying outside the fish). These questions can only be answered by checking the concrete algorithm used to compute the eigenvalues of Tn(a) .•
Notes. Henry Landau [114], [115], [116] was the first to study c-pseudospectra of Toeplitz matrices and equality (3.22) (for smooth symbols) is in principle already in his papers. Independently, equality (3.22) (for symbols in the Wiener algebra W) was discovered by Reichel and Trefethen [140]. These three authors derived (3.22) with the help of different methods. The approach presented here and equality (3.22) for symbols in PC and even for locally normal symbols is from [23]. Theorem 3.17 appeared explicitly in the paper [145] by Roch and one of the authors for the first time. For matrices (= operators on en), Theorem 3.15 is a simple fact. For arbitrary Hilbert space operators (or, more generally, for elements of arbitrary unital C*-algebras), this was first proved by T. Finck and T. Ehrhardt (see [145]). Example 3.16 is taken from [26] and is based on computations done by H. Heidler and P. Santos. Beautiful plots of pseudospectra of several (not necessarily Toeplitz) matrices can be found in [17], [140], [170], and [171]. Examples like Example 3.16 were discussed by Reichel and Trefethen [140] as well as by Beam and Warming [17]. The latter paper also pays attention to algorithms for computing Toeplitz eigenvalues. We will return to this problem in Section 5.8. Finally, we note that with each trigonometric polynomial
q
a(t) = L aktk (t E T)
k=-p
we may associate not only the sequence {Tn (a)} of truncated Toeplitz matrices but also the sequence {Cn (a)} of its so-called Toeplitz circulant cousins [17]; the matrix Cn(a) is the circulant n x n matrix whose first row is
(ao al ... aq 0 ... 0 a_ p ... a-I)
in case n 2: p + q + 1. The eigenvalues of the circulant Cn(a) are
where WI, ... ,Wn are the n solutions of wn = 1. Clearly, sp Cn (a) asymptotically fills in a(T). Accordingly, one of the conclusions of [17] is that "the numerical Toeplitz spectrum approaches the spectrum of its Toeplitz circulant cousin as n ----t 00."


 80 3. Norms of Inverses and Pseudospectra
3.6 Pseudospectra of Infinite Toeplitz Matrices
Corollary 3.18(c) does not relate the pseudospectrum of a large Toeplitz matrix Tn (a) to the spectrum of T(a) but to the pseudospectrum of T(a). Thus, it is desirable to know more about the pseudospectra of infinite Toeplitz matrices. Let ~e := {A E C : IAI ::; E}. If X is a Banach space and A E l3(X), we always have sp A + ~e C sPe A, (3.23)
where sp A + ~e := {{.l + v : {.l E sp A: v E ~e }. Indeed, if A ~ sPe A, then
E < II (A - AI) -111- 1, which implies that A - AI - 8I is invertible whenever
181 ::; E.
The following two theorems provide additional information about the pseudospectra of Toeplitz operators on l2. We let sPo A := sp A.
Theorem 3.19. If E :?:: 0 and a E £00, then
spT(a) + ~e C SPe T(a) C convR(a) + ~e.
Proof. The left inclusion is a special case of (3.23). For E = 0, the right inclusion is the Brown-Halmos theorem (Theorem 1.18). In the case E > 0, the right inclusion can be shown by arguments similar to those of the proof of Theorem 1.18.•
If spT(a) = conv R(a), which happens, for instance, if a E C and R(a) is the boundary of some convex set or if a is any function in £00 for which convR(a) is a line segment, then Theorem 3.19 tells us that
sPe T(a) = convR(a) + ~e'
However, in general both inclusions of Theorem 3.19 may be proper.
Theorem 3.20. Given E > 0, there exist a and b in the Wiener algebra W such that
spT(a) + ~e # SPe T(a), SPe T(b) # convR(b) + ~e'
A full proof is in [30]. We here confine ourselves to the following. Suppose a E Wand R(a) = a(T) is the half-circle {z E T : Imz :?:: O}. Then T(a) is invertible due to Theorem 1.15. Hence, if E > 0 is small enough, then
IIT- 1 (a)11 < liE, which implies that 0 ~ sPe T(a) although 0 E conv R(a) + ~e . Second, put
{
2ill
b(eill ) = e. for 0::; () < 7r,
e- 2,1I for 7r::; () < 27r. (3.24)


 3.6 Pseudospectra of Infinite Toeplitz Matrices 81
If ei8 traverses T, then b(ei8 ) twice traces out the unit circle, once in the positive and once in the negative direction. The Fourier coefficients of bare
bo = 0, b2 = L 2 = 1/2, bn = 0 if n =f. ±2 is even,
bn = 4/(7ri(n2 - 4)) if n is odd.
Therefore b E W. Theorem 1.15 implies that spT(b) = T, but we can show that SP3/4T(b) = 6.7/ 4 , which is larger than T + ~3/4'
Note. The above two theorems were established in our paper [30] with Grudsky.


 4
Moore-Penrose Inverses and Singular Values
4.1 Singular Values of Matrices
Let H be a Hilbert space and let A be a bounded linear operator on H. Then sp A*A C [0,00), and the non-negative square roots of the numbers in sp A *A are called the singular values of A. The set of the singular values of A will be denoted by E(A),
E(A):= {s E [0,00): S2 E spA*A}.
It is well known (see, e.g., [132, p. 296]) that
spA* Au {O} = spAA* U {O},
whence E(A*) U {O} = E(A) U {O}.
(4.1)
Singular value decomposition. We think of n x n matrices as operators on en, where en is equipped with the l2 norm. If An is an n x n matrix, then A~An has n eigenvalues >'k(A~An) and we can order them so that
For the sake of convenience, let us also put so(An ) = O.


 84 4. Moore-Penrose Inverses and Singular Values
Theorem 4.1. If An E B(Cn ), then there exist unitary matrices Un' Vn E
B(C n ) such that
(4.2)
This theorem is well known and proved in the majority of texts on linear algebra. The representation (4.2) is called the singular value decomposition of A.
Interpretation as approximation numbers. For j E {O, 1, ... , n}, let
F;n) denote the collection of all n x n matrices of rank at most j,
and define the jth approximation number of a matrix An E B(Cn ) as
Since F;n) is a closed subset of B(Cn ), the infimum in (4.3) is actually attained, i.e., we can also write
Clearly, dist(An , FJn») = IIAn II and dist(An , F~n») = O.
Theorem 4.2. If An E B(Cn ), then
(4.4)
for every k E {O, 1, ... , n}.
This is again a well-known result. It was established by Dz.E. Allakhverdiev (1957) and M. Fiedler and V. Ptak (1962) for general compact Hilbert space operators and led A. Pietsch to the introduction of the approximation numbers for compact Banach space operators; see [132, p. 293]. For a proof we refer to [87, Theorem II.2.1J. Note that by virtue of Theorem 4.1 the equality (4.4) is equivalent to saying that if 0 ~ al ~ a2 ~ ... ~ an, then
The latter equality even holds if en is equipped with any norm (see [131, Theorem 11.11.3]).


 4.2 The Lowest Singular Value 85
4.2 The Lowest Singular Value
Since the norm of a diagonal matrix is the maximum of the moduli of the
diagonal entries, we obtain from Theorem 4.1 that if An E B(Cn ), then
(A ) = {l/IIA~lll if An is invertible,
Sl n 0 if An is not invertible. (4.5)
Thus, if {An} = {An }::"=l is a sequence of n x n matrices An, we have
(4.6)
This shows that the question of whether the lowest singular value converges to zero is closely connected with the stability of the sequence. More precisely,
liminf sl(An ) > 0 {=::} {An} is stable.
n-+oo (4.7)
In the case where {An} = {Tn (a)} is the sequence of the truncations of some Toeplitz matrix, we can have recourse to the results of Chapter 2.
Theorem 4.3. Suppose a E £00 is locally sectorial on T or a E PC. Then the following are equivalent:
(i) sl(Tn(a)) -+ 0;
(ii) liminfn -+oo Sl (Tn (a)) = 0;
(iii) {Tn(a)} is not stable;
(iv) T(a) is not invertible.
If a E £00 is locally normal on T, then
the limit being zero if T( a) is not invertible.
Proof (i) =} (ii). Trivial. (ii) =} (iii). Immediate from (4.7). (iii) =} (iv). Theorem 2.18 and Corollary 2.19. (iv) =} (i). If limsups1(Tn(a)) > 0, then, by (4.5), there is a sequence
nk -+ 00 such that IIT;k1 (a)11 :::; M < 00 with some M independent of nk. Since Proposition 2.3 remains true with {Tnk(a)} in place of {An}, it follows that T(a) must be invertible. Finally, (4.8) results from (4.5) and (3.16) (and the discussion after Corollary 3.13) .•
For some recent results on the asymptotics of s1 (Tn (a)) for noninvertible operators T(a) see also [151], [152], and [29].


 86 4. Moore-Penrose Inverses and Singular Values
Example 4.4: Cauchy-Toeplitz matrices. Let "¢/ E PC be as in Examples 1.7 and 1.24, i.e., suppose
Tn("¢/) = (_._1_)n
J - k + 'Y j,k=! bE C\Z).
From what was said in Example 1.24 and from Theorem 4.3 we conclude that
4.3 The Splitting Phenomenon
We say that the singular values of a sequence {An} of n X n matrices An have the splitting property if there are Cn -+ 0 and d > 0 such that
:E(An ) C [O,cn ] U [d,oo) for all n ~ 1, (4.9)
and the singular values of {An} are said to enjoy the k-splitting property if there exist en -+ 0 and d > 0 such that (4.9) holds and, for all sufficiently large n, exactly k singular values of An lie in [0, cn ] while the remaining n - k singular values of An belong to [d,oo). Equivalently, the singular values of {An} possess the k-splitting property if and only if
lim sk(An ) = 0 and liminf sk+I(An ) > o.
n~oo n~oo
The purpose of this section is to prove the following result.
Theorem 4.5. Let a E PC. If T(a) is Fredholm of index k E Z, then the singular values of {Tn(a)} have the Ikl-splitting property, i.e.,
IfT(a) is not Fredholm, then
lim sk(Tn(a)) = 0 for each k ~ 1.
n-+oo
(4.10)
(4.11)
Note that so(Tn(a)) = 0 by definition. Figures 24 to 29 illustrate Theorem 4.5. The proof is divided into several steps.
Lemma 4.6. If An, B n , Cn are n x n matrices, then
for every k E {I, ... , n} .


 4.3 The Splitting Phenomenon 87
1.5 Fig. 24
0.5
o
-0.5
-I
-1.5
0.5 1.5 2
-2 L-_-'--_-L.-_---'-_-----'--_-----'-_-----'~ _ _'__________.J
-2 -1.5 -I -0.5 0
Figure 24 shows the essential range of the symbol a(t) = 0.7t + t 5 (t E T). We have wind(a, 0.01) = wind(a, 0.1) = 5.
Proof. If An and Cn are invertible, this follows easily from Theorem 4.2. The case of singular An and Bn can be reduced to the situation in which An and Cn are invertible by a perturbation argument.•
Proposition 4.7. If a E PC and T(a) is Fredholm of index k, then
liminf Slkl+l (Tn (a)) > O.
n->oo
Proof. For the sake of convenience, we replace k by -k. We can then write
a = bXk where n(t) := tk (t E T), b E PC, and T(b) is invertible (Theorems 1.10 and 1.23). Without loss of generality assume k ~ 0; otherwise consider adjoints. Because IITn(X-k)11 = 1, we obtain from Lemma 4.6 that
Sk+l (Tn (bn)) = Sk+1 (Tn(bXk)) IITn(X-k)11
~ sk+1(Tn(bXk)Tn(X-k)) = Sk+l(Tn(b) - PnH(bXk)H(Xk)Pn ),
the latter equality resulting from (2.13) and the identities
H(X-k) = H(n), H(X-k) = o.
Since dim 1m H (Xk) = k, we see that
Fk := PnH(bxk)H(n)Pn E :F~n),


 88 4. Moore-Penrose Inverses and Singular Values
0.9
0.8
0.7
0.6
0.5
0.4
0.3
0.2
0.1 Fig. 25
oLL_--,-_~~~"""""",,,,,,,,,,,,,,-",----,-----,-----,--~
o 10 20 30 40 50 60 70 80 90 100
In Figure 25 we plotted the singular values 8j(Tn (a - 0.01)) for 3 ::; n ::; 100 and 1 ::; j ::; min{n, 3D} in case a is as in Figure 24. In accordance with Theorem 4.5, the five lowest singular values go to zero, while the remaining singular values stay away from zero. The figure shows that, for example, the 6th singular value is waiting for the 7th, 8th, 9th singular values before making the next step downward. This is certainly a phenomenon caused by the high symmetry in Figure 24.
whence
8k+l(Tn (b) - Fk)
= inf {IITn(b) - Fk - Gn- k - 1 11 : Gn -k-1 E F~~k_l}
2: inf{IITn(b) - Hn-dl :Hn-1 E F~~l} = 81(Tn(b)).
As T(b) is invertible, Theorem 4.3 shows that 81 (Tn (b)) is bounded away from zero.•
Proposition 4.8. If a E PC and T(a) is Fredholm of index k, then
Proof. Replace again k by -k and assume k > 0 for the sake of definiteness. We write a = Xkb as in the preceding proof. Using Proposition 2.12 and


 4.3 The Splitting Phenomenon 89
0.9
0.8
0.7
0.6
0.5
0.4
0.3
0.2
0.1 Fig. 26
oLL_--,-~~="':::::::::::.::=====----o._---"-_~
o 10 20 30 40 50 60 70 80 90 100
Let a be as in Figure 24. In Figure 26 we plotted the singular values sj(Tn(a - 0.1)) for 1 :::; j :::; min{n,30} versus 3 :::; n :::; 100. Again Theorem 4.5 is convincingly confirmed, which says that the five lowest singular values must tend to zero, while the remaing singular values stay away from zero. However, the way the sigular values decay differs from the pattern of Figure 25.
Lemma 4.6 we get
sk(Tn(Xkb)) sk(Tn(Xk)Tn(b) + PnH(Xk)H(b)Pn )
< IITn(b)llsk(Tn(Xk) + PnH(Xk)H(b)PnT;;l(b))
for all sufficiently large n. Put
An := Tn(Xk) + PnH(Xk)H(b)PnT;;l(b)
and write An = AnQn-k + AnPn- k with Qn-k := I - Pn- k. Since
rank(AnPn- k) :::; rank Pn-k = n - k,
we obtain from Theorem 4.2 that
and hence, we are left with showing that IIAnQn-kll ---+ 0 as n ---+ 00. As T(Xk)Qn-k = 0, we have
AnQn-k = PnH(Xk)H(b)Pnt;;l(b)Qn_k' (4.12)


 90 4. Moore-Penrose Inverses and Singular Values
2,-----r---,----,---..--,---,-----,------,
1.5 Fig. 27
0.5
o
-0.5
-I
-1.5
o 0.5 1.5 2
-0.5
_2'---'-------'---------'-_ _'--_...L-_-'-_----'--_-----'
-2 -1.5 -I
In Figure 27 we see the essential range of the symbol a(t) = 0.7t +
0.lt4 + t 5 (t E T). Clearly, wind(a,O.l) = 5.
Because H(Xk) is compact, Pn --+ I strongly, and
we deduce from Lemma 2.8 that IIAnQn-kll --+ 0, as desired.•
Obviously, the first part of Theorem 4.5 is simply the union of Propositions 4.7 and 4.8.
More general symbols. We remark that the proofs given above actually yield more than part of Theorem 4.5. Namely, let nO denote the set of all symbols b E UXJ for which {Tn(b)} is stable and let n be the set of all symbols a E LOO such that aXk E nO for some k E Z. For instance, we know that locally sectorial symbols belong to n and we also have
G(C + H oo ) U G(C + Hoo) U G(PQC) c n,
where G(B) stands for the invertible elements of a unital Banach algebra B, C + Hoo and C + Hoo are as in Section 1.6, and PQC is the algebra of all piecewise quasicontinuous functions (see, e.g., [39, Section 3.35 and Chapter 7]). By Theorem 2.7, n is a proper subset of L=. Repeating the proofs of Propositions 4.7 and 4.8 we arrive at the conclusion that (4.10) holds whenever a E nand T(a) is Fredholm of index k.