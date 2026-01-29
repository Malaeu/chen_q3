---
title: "Theory of reproducing kernels"
authors:
  - "Nachman Aronszajn"
date: "1950-00-00 1950"
publication: "Transactions of the American Mathematical Society"
doi: "10.1090/S0002-9947-1950-0051437-7"
url: "https://www.jstor.org/stable/1990404"
zotero:
  attachment_key: "PMKIIXRV"
  parent_key: "XGS462W3"
  item_id: 1952
  attachment_item_id: 1987
---

THEORY OF REPRODUCING KERNELS(')
BY
N. ARONSZAJN
Preface
The present paper may be considered as a sequel to our previous paper in the Proceedings of the Cambridge Philosophical Society, Theorie générale de noyaux reproduisants—Première partie (vol. 39 (1944)) which was written in 1942-1943. In the introduction to this paper we outlined the plan of papers which were to follow. In the meantime, however, the general theory has been developed in many directions, and our original plans have had to be changed. Due to wartime conditions we were not able, at the time of writing the first paper, to take into account all the earlier investigations which, although sometimes of quite a different character, were, nevertheless, related to our subject. Our investigation is concerned with kernels of a special type which have been used under different names and in different ways in many domains of mathematical research. We shall therefore begin our present paper with a short historical introduction in which we shall attempt to indicate the different manners in which these kernels have been used by various investigators, and to clarify the terminology. We shall also discuss the more important trends of the application of these kernels without attempting, however, a complete bibliography of the subject matter. In Part I, we shall discuss briefly the essential notions and results of our previous paper and give a further development of the theory in an abstract form. In Part II, we shall illustrate the results obtained in the first part by a series of examples which will give new developments of already known applications of the theory, as well as some new applications.
Table of Contents
Historical Introduction. 338 Part I. General Theory. 342 1. Definition of reproducing kernels. 342 2. Résumé of basic properties of reproducing kernels. 343 3. Reproducing kernels of finite-dimensional classes. 346 4. Completion of incomplete Hubert spaces. 347 5. The restriction of a reproducing kernel. 350 6. Sum of reproducing kernels. 352
Presented to the Society, December 28, 1948, under the title Hubert spaces and conformai mappings; received by the editors November 26, 1948. (') Paper done under contract with the Office of Naval Research, N5ori 76-16-NR 043-046, Division of Engineering Science, Harvard University.
337


 338 N. ARONSZAJN [May
7. Difference of reproducing kernels. 354 8. Product of reproducing kernels. 357 9. Limits of reproducing kernels. 362 10. Construction of a r.k. by resolution of identity. 368 11. Operators in spaces with reproducing kernels. 371 12. The reproducing kernel of a sum of two closed subspaces. 375 13. Final remarks in the general theory. 380 Part II. Examples. 384 1. I ntroductory remarks. 384 (1) Bergman's kernels. 384 (2) Harmonic kernels. 386 2. Comparison domains. 387 3. The difference of kernels. 388 4. The square of a kernel introduced by Szegö. 391 5. The kernel H{z, zi) for an ellipse. 393 6. Construction of H(z, z¡) for a strip. 394 7. Limits of increasing sequences of kernels. 396 8. Construction of reproducing kernels by the projection-formula of §12, I. 397 Bibliography. 401
Historical Introduction
Examples of kernels of the type in which we are interested have been known for a long time, since all the Green's functions of self-adjoint ordinary differential equations (as also some Green's functions—the bounded onesof partial differential equations) belong to this type. But the characteristic properties of these kernels as we now understand them have only been stressed and applied since the beginning of the century. There have been and continue to be two trends in the consideration of these kernels. To explain them we should mention that such a kernel K(x, y) may be characterized as a function of two points, by a property discovered by J. Mercer [l](2) in 1909. To the kernel K there corresponds a well determined class F of functions/(x), in respect to which K possesses the "reproducing" property (E. H. Moore [2]). On the other hand, to a class of functions F, there may correspond a kernel K with "reproducing" property (N. Aronszajn [4]). Those following the first trend consider a given kernel K and study it in itself, or eventually apply it in various domains (as integral equations, theory of groups, general metric geometry, and so on). The class F corresponding to K may be used as a tool of research, but is introduced a posteriori (as in the work of E. H. Moore [2], and more recently of A. Weil [l], I. Gelfand and D. Raikoff [l], and R. Godement [l, 2]). In the second trend, one is interested primarily in a class of functions F, and the corresponding kernel K is used essentially as a tool in the study of the functions of this class. One of the basic problems in this kind of investigation is the explicit construction and computation of the kernel for a given class F.
(2) Numbers in brackets refer to the bibliography at the end of the paper.


 1950] THEORY OF REPRODUCING KERNELS 339
The first of these trends originated in the theory of integral equations as developed by Hubert. The kernels considered then were continuous kernels of positive definite integral operators. This theory was developed by J. Mercer [l,2] under the name of "positive definite kernels" and on occasion has been used by many others interested in integral equations, especially during the second decade of this century. Mercer discovered the property
n
(1) ^ K(yi, yi)\&j è 0, yi any points, £,•any complex numbers(3), i,t-l
characterizing his kernels, among all the continuous kernels of integral equations. To this same trend belong the investigations of E. H. Moore [l, 2] who, during the second and third decades of the century, introduced these kernels in the general analysis under the name of "positive hermitian matrices" with a view to applications in a kind of generalization of integral equations. Moore considered kernels K(x, y) defined on an abstract set E and characterized by the property (1). He discovered the theorem now serving as one of the links between the two trends, proving that to each positive hermitian matrix there corresponds a class of functions forming what we now call a Hubert space with a scalar product (/, g) and in which the kernel has the reproducing property.
(2) f(y) = (/(*), K(x, y».
Also to the same trend (though seemingly without any connection to previous investigations) belongs the notion introduced by S. Bochner [2] during the third decade of the century under the name of "positive definite functions." Bochner considered continuous functions <p(x) of real variable x such that the kernels K(x, y) =<p(x —y) conformed to condition (1). He introduced these functions with a view to application in the theory of Fourier transforms. The notion was later generalized by A. Weil [l ] and applied by I. Gelfand and D. Raikoff [l], R. Godement [l, 2], and others to the investigation of topological groups under the name of positive definite functions or functions of positive type. These functions were also applied to general metric geometry (the Hubert distances) by I. J. Schoenberg [l, 2], J. v. Neumann and I. J. Schoenberg [l], and S. Bochner [3]. The second trend was initiated during the first decade of the century in the work of S. Zaremba [l, 2] on boundary value problems for harmonic and biharmonic functions. Zaremba was the first to introduce, in a particular case, the kernel corresponding to a class of functions, and to state its reproducing property (2). However, he did not develop any general theory, nor did he give any particular name to the kernels he introduced. It appears that nothing was done in this direction until the third decade when S. Berg
(3) Mercer used only real numbers £; as he considered only real kernels K.


 340 N. ARONSZAJN [May
man [l] introduced kernels corresponding to classes of harmonic functions and analytic functions in one or several variables. He called these "kernel functions." They were introduced as kernels of orthogonal systems in these classes for an adequate metric. The reproducing property of these kernels was noticed by Bergman [l] (also by N. Aronszajn [l]), but it was not used as their basic characteristic property as is done at present. In the third and fourth decades most of the work was done with kernels which we shall call Bergman's kernels, that is, kernels of classes of analytic functions/of one or several complex variables, regular in a domain D with the quadratic metric
f \&dr.
JD
A quantity of important results were achieved by the use of these kernels in the theory of functions of one and several complex variables (Bergman [4, 6, 7], Bochner [l]), in conformai mapping of simply- and multiply-connected domains (Bergman [ll, 12], Zarankiewicz [l] and others), in pseudoconformal mappings (Bergman [4, 5, 8, 9], Welke [l], Aronszajn [l], and others), in the study of invariant Riemannian metrics (Bergman [ll, 14], Fuchs [l, 2]), and in other subjects. The original idea of Zaremba to apply the kernels to the solution of boundary value problems was represented in these two decades by only a few papers of Bergman [l, 2, 3, 10]. Only since the last war has this idea been put into the foreground by a series of papers by Bergman [13], and Bergman and Schiffer [l, 2, 3]. In these investigations, the kernel was proved to be a powerful tool for solving boundary value problems of partial differential equations of elliptic type. By the use of variational methods going back to Hadamard, relations were established between the kernels corresponding to classes of solutions of different equations and for different domains (Bergman and Schiffer [l, 3]). For a partial differential equation, the kernel of the class of solutions in a domain was proved to be the difference of the corresponding Neumann's and Green's functions (Bergman and Schiffer [l, 3]) (in the special case of the biharmonic equation a relation of this kind was already noticed by Zaremba). Parallel to this revival of the application of kernels to partial differential equations there is developing a study of the relationship between these kernels and Bergman's kernels of analytic functions (Bergman [12], M. Schiffer [l, 2]). Also the application of kernels to conformai mapping of multiply-connected domains has made great progress as all the important mapping functions were proved to be simply expressible by the Bergman's kernel (Bergman [ll, 12], P. Garabedian and M. Schiffer [l], Garabedian [l], and Z. Nehari [l, 2]). Quite recently, the connection was found between the Bergman's kernel and the kernel introduced by G. Szegö (P. Garabedian [l]). In 1943, the author ([4] also [6]) developed the general theory of repro


 1950] THEORY OF REPRODUCING KERNELS 341
ducing kernels which contains, as particular cases, the Bergman kernelfunctions. This theory gives a general basis for the study of each particular case and allows great simplification of many of the proofs involved. In this theory a central role is played by the reproducing property of the kernel in respect to the class to which it belongs. The kernel is defined by this property. The simple fact was stressed that a reproducing kernel always possesses property (1) characteristic of positive hermitian matrices (in the sense of E. H. Moore). This forms the second link between the two trends in the kernel theory (the theorem of E. H. Moore forming the first link was mentioned above). The mathematicians working in the two trends seem not to have noticed the essential connections between the general notions they were using. At present the two concepts of the kernel, as a positive hermitian matrix and as a reproducing kernel, are known to be equivalent and methods elaborated in the investigations belonging to one trend prove to be of importance in the other. We should like to elaborate here briefly on the matter of the terminology which has been used by various investigators. As we have seen above, different names have been given to the kernels in which we are interested. When the kernels were used in themselves, without special or previous consideration of the class to which they belonged, they were called "positive definite kernels," "positive hermitian matrices," "positive definite functions," or "functions of positive type." In cases where they were considered as determined, and in connection with a class of functions, they were called "kernel functions" or "reproducing kernels." It is not our intention to settle here the question of terminology. Our purpose is rather to state our choice and to give our reasons for it together with a comparison of the terminology we have chosen with that used by other authors. It would seem advisable to keep two names for our kernels, the function of each name being to indicate immediately in what context the kernel under consideration is to be taken. Thus, when we consider the kernel in itself we shall call it (after E. H. Moore) a positive matrix^), in abbreviation, p. matrix, or p. m. When we wish to indicate the kernel corresponding to a class of functions we shall call it the reproducing kernel of the class, in abbreviation, r. kernel or r.k. As compared to other terminology, we believe that the name "positive definite function" or perhaps better "function of positive type" will probably continue to be used in the particular case when the kernel is of the form <p(x—y), x, y belonging to an additive group. This term has been used in a few instances for some more general kernels, but we believe that it would prove to be more convenient if it were restricted to the particular case
(4) We drop here the adjective "hermitian" since the condition that the quadratic form (1) be positive implies the hermitian symmetry of the matrix.


 342 N. ARONSZAJN [May
mentioned above. Although the name of "positive definite kernels" would seem, somehow, more adequate than "positive matrices," especially since it was introduced first, we have chosen rather the term used by E. H. Moore. This is because we wish to reserve the notion of positive definite kernel for more general kernels which would include the positive definite matrices as well as some other non-bounded kernels (such as the kernels of general positive definite integral operators and also the recently introduced pseudo-reproducing kernels [Aronszajn 5, 6]). On the other hand, when we have in mind the kernel corresponding to a given class of functions, the simplest terminology is to call it "the kernel of the class" or "the kernel belonging to the class." But when some ambiguity is to be feared, or when we wish to stress its characteristic property, we use the adjective "reproducing."
Part I. General theory
1. Definition of reproducing kernels. Consider a linear class F of functions f(x) defined in a set E. We shall suppose that F is a complex class, that is, that it admits of multiplication by complex constants. Suppose further that for/GFis defined a norm ||/[ (that is, a real number satisfying: ||/|| £0, J|/|| = 0 only for /=0, \\cf\\= \c\ |/||, ||/+g|| ^\\f\\ +\\g\\) given by a quadratic hermitian form Q(f)
U/H=2 QU).
Here, a functional Q(f) is called quadratic hermitian if for any constants ¿i, £2 and functions f, f2 of F
Qitifi+ £2/2-) Ih |Wi) + tM(fi, h) + Uü(U, fi) + I£2IW2).
Q(fi,f2) = Q(f2,fi) is the uniquely determined bilinear hermitian form corresponding to the quadratic form Q(f). This bilinear form will be denoted by (fi, f2) = Q(fi, f2) and called the scalar product corresponding to the norm jj/|| (or the quadratic metric ||/||2). We have
. Il/ll=2(/,/)•
The class F with the norm, || ||, forms a normed complex vector space. If this space is complete it is a Hubert space. If F is a class of real-valued functions forming a real vector space (that is, admitting of multiplication with only real constants), if the norm, || ||, in F is given by ||/||2 = (?(/) with an ordinary quadratic form Q (that is, for real
&, £2,Q(^i+^f2)=^Q(fi)+2^2Q(fi,f2)+&Q(f2), where Q(f,f2) is the cor
responding bilinear symmetric form), and if F is a complete space, it is a real Hubert space. The scalar product is given there by (f, f2) =Q(fi,f2). Every class F of real functions forming a real Hubert space determines a


 1950] THEORY OF REPRODUCING KERNELS 343
complex Hubert space in the following way: consider all functions fi+if2 with fi and f2 in F. They form a complex vector space Fc in which we define the norm by ||/i+í/2||2 = ||/i||2 + ||/2||2. Fc is a complex Hubert space. The complex Hubert spaces F determined in this way by real Hubert spaces are characterized by the two properties : (1) ií/G-F,/GF (/is the conjugate complex function of/),
(2) ||/!l=/
Let F be a class of functions defined in E, forming a Hubert space (complex or real). The function K(x, y) of x and y in £ is called a reproducing kernel (r.k.) oí F ii 1. For every y, K(x, y) as function of x belongs to F. 2. The reproducing property: for every yG-E and every/G^",
f(y) = (f(x),K(x,y))x.
The subscript x by the scalar product indicates that the scalar product applies to functions of x. If a real class F possesses a r.k. K(x, y) then it is immediately verified that the corresponding complex space Fc possesses the same kernel (which is realvalued) : From now on (unless otherwise stated) we shall consider only complex Hubert spaces. As we have seen there is no essential limitation in this assumption. It will be useful to introduce a distinction between the terms subclass and subspace. When Fi and F2 are two classes of functions defined in the same set E, Fi is a subclass of F2 if every / of Fi belongs to F2. Fi is a subspace of F2 if it is a subclass of F2 and if for every /G-Fi, ||/||i = ||/||2 (|| ||i and || ||2 are the norms in Fi and F2 respectively). Fi(ZF2 means that Fi is a subclass of F2. 2. Résumé of basic properties of reproducing kernels. In the following, F denotes a class of functions f(x) defined in E, forming a Hubert space with the norm ||/|| and scalar product (fi,f2). K(x, y) will denote the corresponding reproducing kernel. The detailed proofs of the properties listed below may be found in [Aronszajn, 4]. (1) If a r.k. K exists it is unique. In fact, if another K'(x, y) existed we would have for some y
0 < \\K(x, y) - K'(x, y)\\2 = (K - K'', K - K') = (K - K', K) - (K - K', K') = 0
because of the reproducing property of K and K'. (2) Existence. For the existence of a r.k. K(x, y) it is necessary and sufficient that for every y of the set E, f(y) be a continuous functional of / running through the Hubert space F. In fact, if K exists, then \f(y)\ ^\\f\\(K(x,y), K(x,y)yi2 = K(y,yyi2\\f\\.


 344 N. ARONSZAJN [May
On the other hand if f(y) is a continuous functional, then by the general theory of the Hubert space there exists a function gy(x) belonging to F such that/(y) = (f(x), gy(x)), and then if we put K(x, y) =gy(x) it will be a reproducing kernel. (3) K(x, y) is a positive matrix in the sense of E. H. Moore, that is, the quadratic form in £1, • • • , £„
n
(1) E K(yi,y,)Ui
«,í=i
is non-negative for all fi, • • • , fn in E. This is clear since expression (1) equals || E" K(x, y¿)£,||2, following the reproducing property. In particular it follows that
K(x, x) ^ 0, K(x, y) = K(y, x), ¡K(x, y)\2 g K(x, x) K(y, y).
(4) The theorem in (3) admits a converse due essentially to E. H. Moore: to every positive matrix K(x, y) there corresponds one and only one class of functions with a uniquely determined quadratic form in it, forming a Hubert space and admitting K(x, y) as a reproducing kernel. This class of functions is generated by all the functions of the form ~^akK(x, y). The norm of this function is defined by the quadratic form || 23a<fcK(x, y«;)||2= 23 ^K(yt, fi)hii- Functions with this norm do not as yet form a complete Hubert space, but it can be easily seen that they may be completed by the adjunction of functions to form such a complete Hubert space. This follows from the fact that every Cauchy sequence of these functions (relative to the above norm) will converge at every point x towards a limit function whose adjunction to the class will complete the space. (5) If the class F possesses a r.k. K(x, y), every sequence of functions {/„ J which converges strongly to a function/ in the Hubert space F, converges also at every point in the ordinary sense, lim fn(x) =f(x), this convergence being uniform in every subset of E in which K(x, x) is uniformly bounded. This follows from
If(y) - My) | = | (f(x) - fn(x),K(x, y)) I á ||/ - /„|| ||JC(«,y)||
= \\f-f\\(K(y, y)Y'K
If /„ converges weakly to/, we have again fn(y)—>f(y) for every y (since, by the definition of the weak convergence, (fn(x), K(x, y))—>[f(x), K(x, y)). There is in general no increasing sequence of sets FiCF^C ■ ■ ■—>F in each of which /„ converges uniformly to / If a topology (a notion of limit) is defined in E and if the correspondence y*-±K(x, y) transforms £ in a continuous manner into a subset of the space F, then the weakly convergent sequence {/„} converges uniformly in every compact set EiCZE. In fact Ei is transformed into a compact subset of the


 1950] THEORY OF REPRODUCING KERNELS 345
space F. For every e>0 we can then choose a finite set (yi, • • • , yi) C-Ei so that for every yG-Ei there exists at least one y¡t with ||i£(x, y)—K(x, y*)|| ge/4ilf, where ilf=l.u.b.n ||/„||. Further, if we choose n0 so that for n>no, |/(y*) —/»(y*) | <e/4, we shall obtain for yG-Ei
If(y)- My)I= I(Ay-) Ay*)+) C/(*-) /»(y*)+)(/-(y*-)/»(y)I)
á | Ay») - /„(y>) | + | (f(x) - fn(x), K(x, y) - K(x, yk)) \
á 4 + ïf - /«IlH^(«y.)- K(x,yk)\á\ 4 + 2M-i- < e.
4 4 4M
The continuity of the correspondence y<->K(x, y) is equivalent to equicontinuity of all functions of F with ||/|| <M for any M>0. This property is satisfied by most of the classes with reproducing kernels which are usually considered (such as classes of analytic functions, harmonic functions, solutions of partial differential equations, and so on). (6) If the class F with the r.k. K is a subspace of a larger Hubert space §, then the formula
/(y) = (h,K(x,y))x
gives the projection / of the element h of ¿p on F. In fact h=f+g, where g is orthogonal to the class F. K(x, y) as a function of x belongs to F and so we have (h, K(x, y)) = (f+g, K(x, y)) = (/, K (x, y)) =f(y) by the reproducing property. (7) If F possesses a r.k. K, then the same is true of all closed linear subspaces of F, because if/(y) is a continuous functional of/running through F, it is so much the more so if / runs through a subclass of F. If F' and F" are complementary subspaces of F, then their reproducing kernels satisfy the equation K'+K" = K. (8) If F possesses a r.k. K and if {gn\ is an orthonormal system in F, then for every sequence {a„} of numbers satisfying
00
22 | a„|2 < oo, i
we have
Z | «» | | gn(x) | ^ K(x, xy2( ¿ | an \*\ .
In fact, for a fixed y, the Fourier coefficients of K(x, y) for the system {gn ] are
(K(x, y), gn(x)) = (gn(x), K(x, y)) = gn(y).


 346 N. ARONSZAJN [May
Consequently
Z gn(yY á (K(x, y), K(x, y))x = K(y, y).
i
Therefore
/ x \l/2 / «o \l/2
Z I«-IIgn( |x)£ ( Z I«»I') (^Z I«»( |*2)j
(» \ 1/2
ZW2) •
3. Reproducing kernels of finite-dimensional classes. If F is of finite dimension n, let Wi(x), ■ ■ • , w„(x) be n linearly independent functions of F. All functions/(x) of Fare represen table in a unique manner as
(1) /(*) = Z i~kWk(x), Çkcomplex constants.
i
The most general quadratic metric in F will be given by a positive definite hermitian form
(2) 11/1=12Z «ata,.
i, 3= 1
The scalar product has the form
(3) (/, g) = Z «ijftff. w/zereg = Z f**"*.
1,3
It is clear that
(4) OK, = (w¿, Wj).
Therefore the matrix {«¿ij is the Gramm's matrix of the system {w*}. This matrix always possesses an inverse. Denote by {ßa} the conjugate of this inverse matrix. We have then
(5) Z aaßik = 0 or 1 following as i j¿ k or i = k. i
It is immediately verified that the function
n
(6) K(x, y) = Z ßiiWi(x)u>j(y)
i, 3=1
is the reproducing kernel of the class F with the metric (2). The matrix {ßij} is hermitian positive definite. From the preceding developments we get, clearly, the following theorem.


 1950] THEORY OF REPRODUCING KERNELS 347
Theorem. A function K(x, y) is the reproducing kernel of a finite-dimensional class of functions if and only if it is of the form (6) with a positive definite matrix {ßn\ and linearly independent functions wk(x). The corresponding class F is then generated by the functions wk(x), the functions /GF given by (I) and the corresponding norm \\f\\ given by (2), where {an} is the inverse matrix of
4. Completion of incomplete Hubert spaces. In applications, we often meet classes of functions forming incomplete Hubert spaces, that is, linear classes, with a scalar product, satisfying all the conditions for a Hubert space with the exception of the completeness. For such classes, two problems present themselves. Firstly, the problem of completing the class so as to obtain a class of functions forming a complete Hubert space and secondly, to decide (before effecting the completion of the class) if the complete class will possess a reproducing kernel. A few remarks should be added here about the problem of the completion of a class of functions forming an incomplete Hilbert space. Consider such a class F. It is well known that to this class we can adjoin ideal elements which will be considered as the limits of Cauchy sequences in F, when such a limit is not available in F, and in such a way we obtain an abstract Hilbert space containing the class F as a dense subset. This space, however, will not form a class of functions. In quite an arbitrary way we could realize the ideal elements to be adjoined to Fas functions so as to obtain a complete space formed by a linear class of functions, but, in general, this arbitrary manner of completion will destroy all the continuity properties between the values of the functions and the convergence in the space. In this paper when we speak about the functional completion of an incomplete class of functions F, we mean a completion by adjunction of functions such that the value of a function / of the completed class at a given point y depends continuously on / (as belonging to the Hilbert space) (5). From the existence theorem of reproducing kernels we deduce the fact that a completed class has a reproducing kernel. In this way the problem of functional completion and of the existence of a reproducing kernel in the complete class is merged into one problem. We shall prove here the following theorem:
Theorem. Consider a class of functions F forming an incomplete Hilbert space. In order that there exist a functional completion of the class it is necessary and sufficient that 1° for every fixed y(£E the linear functional f(y) defined in F be bounded; 2° for a Cauchy sequence [fm\ CF, the condition/m(y)—»0 for every y implies ||/m||—>0. If the functional completion is possible, it is unique.
Proof. That the first condition is necessary is immediately seen from the
(6) A more general functional completion was introduced in connection with the theory of pseudo-reproducing kernels (N. Aronszajn [5]).


 348 N. ARONSZAJN [May
existence theorem of reproducing kernels, since the complete class would necessarily have such a kernel. The necessity of the second condition follows from the fact that a Cauchy sequence in F is strongly convergent in the complete space to a function /, and the function / is the limit of fm at every point y of E. Consequently, /= 0 and the norms of fm have to converge to the norm of/ which is equal to zero. To prove the sufficiency we proceed as follows: consider any Cauchy sequence {/„JC-r7. For every fixed y denote by My the bound of the functional f(y) so that
(i) /(y)I á My\\f\\.
Consequently,
\U(y)-fn(y)\ SMy\\fm-fn\\.
It follows that {fn(y)} is a Cauchy sequence of complex numbers, that is, it converges to a number which we shall denote by/(y). In this way the Cauchy sequence {/„} defines a function/ to which it is convergent at every point of E. Consider the class of all the functions /, limits of Cauchy sequences [fn}ClF. It is immediately seen that it is a linear class of functions, and that it contains the class F (since the Cauchy sequence {/„} with/„=/GE is obviously convergent to/). Consider, then, in the so-defined class F, the norm
(2) 11/1=11Hm||/„||
for any Cauchy sequence \fn}(ZF converging to / at every point y. This norm does not depend on the choice of the Cauchy sequence: in fact, if another sequence, {/„' } converges to/at every point y, then/„' —/„ will be a Cauchy sequence converging to zero, and by the second condition the norms ||/n -/n|| converge to zero. Consequently,
| lim ||/I|] - lim ||/„|| | = lim | \\f'n\\- ||/„|| | ^ lim ||/n - /„|| = 0.
On the other hand, it is readily seen that \\f\\l is a quadratic positive form in the class F; it is obviously 0 for /=0, and it is positive for /^0 because of (1). This norm defines a scalar product in F satisfying all the required properties. It remains to be shown that F is complete and contains F as a dense subspace. The second assertion is immediately proved because FC F. For elements of F, the norms || ||, || ||i coincide, and every function /G F is, bydefinition, the limit of a Cauchy sequence {/„} C F everywhere in E. It follows that/is a strong limit of /„ in F since by (2)
lim ||/ -/„||i = lim lim ||/„ - /„|| =0.


 1950] THEORY OF REPRODUCING KERNELS 349
To prove the first assertion, that is, the completeness of F, we shall consider any Cauchy sequence {/„} C F. Since F is dense in F, we can find a Cauchy sequence {/„' } C F such that
Hm ii/; - /„|¡! = 0.
The Cauchy sequence {/„' } converges to a function /GF. This convergence is meant at first as ordinary convergence everywhere in E, but the argument used above shows that the /„' also converge strongly to / in the space F. It follows immediately that/« converges strongly to/. The uniqueness of the complete class is seen from the fact that in the completed class a function/ must necessarily be a strong limit of a Cauchy sequence {/„} CF. Since a reproducing kernel must exist for the completed class, this implies that / is a limit everywhere of the Cauchy sequence {/„} which means that it belongs to the above class F. As the norm of/ has to be the limit of ||/„|| it necessarily coincides with ||/||i. It is also clear that every function/ of F must belong to the completed class. In summing up the above arguments we see that any functional completion of F must coincide with F and have the same norm and scalar product as F. It should be stressed that the second condition cannot be excluded from our theorem. We shall demonstrate this by the following example: Consider the unit circle |z| <1. Take there an infinite sequence of points [zn] such that
£(i-|z„l)< «.
We shall denote by E the set of all points zn, and in E we shall consider the class F of all polynomials in z. It is obvious that the values of a polynomial cannot vanish everywhere in the set E if the polynomial is not identically zero. Consequently the values of a polynomial on the set E determine completely the polynomial. We define the norm for a function/of the class F by the formula
U/H=2(f I#WI'dxdy, z= x+ iy,
J J |z|<l
where p denotes the polynomial whose values on the set E are given by the function /. We see that F satisfies all requirements for a Hilbert space with the exception of completeness. The first condition of our theorem is satisfied but the second is not. To prove the last assertion we take the Blaschke function <p(z) corresponding to {zn}. This function has the following properties
4>0n)= 0, » = 1, 2, 3, - • • ,
| 4>(z)| < 1 for | z | < 1.


 350 N. ARONSZAJN [May
The function <p(z) is a strong limit of polynomials pk(z) in the sense
lim If | <p(z)- pk(z)\2dxdy= 0.
J J |2|<i
Consequently the sequence {pk} is a Cauchy sequence in our class F and the polynomials pk(z) converge at each point z„ to 4>(zn)=0, in spite of the fact that the norms \\pk\\ converge to \\<p\\>0. This example also shows us the significance of condition 2°. We can say that if condition 2° is not satisfied it means that the incomplete class is defined in too small a set. If we added a sequence of points {z„' } of the unit circle with a limit point inside the circle to the set E of our example, then the class of polynomials, considered on this enlarged set Ei with the same norm as above, would satisfy condition 2°. There are infinitely many ways of enlarging the set E where an incomplete class F is defined so as to insure the fulfillment of condition 2°. In the general case we can always proceed as follows. We can consider the abstract completion of the class F by adjunction of ideal elements. This completion leads to an abstract Hilbert space §. To every element of § there corresponds a well determined function f(x) defined on the set (the limit of Cauchy sequences in F converging to this element). But to different elements of § there may correspond the same function/. The correspondence is linear and the functional/(y) are continuous in the whole §. To every point yGF there corresponds an element A¡,G§ such that f(y) = (/, hy), where/ is any element of 1q corresponding to the function f(x). As there are elements of § different from the zero element and which correspond to the function identically zero on E, it is clear that the set of elements hv is not complete in the space §. (This is characteristic of the fact that condition 2° is not satisfied.) To the set of elements hy we can then add an additional set of elements so as to obtain a complete set in §. This additional set will be denoted by E'. We can then extend the functions of our class F in the set E+E' by defining, for any element h(E.E', f(h) = (/, h). This class of functions, so extended in E-r-E', will then satisfy the second condition. We shall complete this section by the following remark: It often happens that for the incomplete class F a kernel K(x, y) is known such that for every y, K(x, y) as function of x belongs to F (or, even more generally, belongs to a Hilbert space containing F as a subspace), this kernel having the reproducing property f(y) = (S(x), K(x, y)) for everyf G.F
It is immediately seen that the first condition of our theorem follows from this reproducing property so that it suffices to verify the second condition in order to be able to apply our theorem. 5. The restriction of a reproducing kernel. Consider a linear class F of


 1950] THEORY OF REPRODUCING KERNELS 351
functions defined in the set E, forming a Hubert space and possessing a r.k. K(x, y). K is a positive matrix. If we restrict the points x, y to a subset EiCZE, K will still be a positive matrix. This means that K will correspond to a class Fi of functions defined in Ei with an adequate norm || ||j. We shall now determine this class Fi and the corresponding norm.
Theorem. If K is the reproducing kernel of the class F of functions defined in the set E with the norm || ||, then K restricted to a subset E1C.E is the reproducing kernel of the class Fi of all restrictions of functions of F to the subset Ei. For any such restriction, fiQ.Fi, the norm ||/i||i is the minimum of ||/|| for all fQF whose restriction to Ei is fi.
Proof. Consider the closed linear subspace FoQF formed by all functions which vanish at every point of Ei. Take then the complementary subspace F' = F&F0. Both F0 and F' are closed linear subspaces of F and possess reproducing kernels K0 and K' such that
(1) K = Ko + K'.
Since K0(x, y), for every fixed y, belongs to F0, it is vanishing for xQEiConsequently,
(2) K(x, y) = K'(x, y), for x G £1.
Consider now the class Fi of all restrictions of F to the set Ei. If two functions/ and g from F have the same restriction/1 in Ei, f—g vanishes on Ei and so belongs to F0. Conversely, if the difference belongs to F0, f and g have the same restriction /1 in Ex. It is then clear that all the functions /G P which have the same restriction /1 in E have a common projection f{ on F' and that the restriction of A' in Ei is equal also to A- It is also clear that among all these functions,/,// is the one which has the smallest norm. Consequently by the definition of the theorem, we can write
(3) llAl»IIxI/Î1I.
The correspondence between fiQ.Fi and // QF' obviously establishes a one-to-one isometric correspondence between the space Fi with the norm ||i and the space F' with the norm || ||. In order to prove that for the class Fi with the norm || ||i the reproducing kernel is given by K restricted to £1, we take any function f1Q.F1 and consider the corresponding function fiQF'. Then, for yG-Ei, A(y) =/i (y) = (f{(x),K'(x,y)). Since K'(x, y), for every y belongs to F', we may now write A(y) = (/il(x), K'(x, y)) = (fi(x), Ki(x, y))i, where Ki(x, y) is the restriction of K'(x, y) (considered as function of x) to the set £1. By hermitian symmetry we obtain from (2)


 352 N. ARONSZAJN [May
K(x, y) = K'(x, y), for every y G Ei
This shows that the restriction Ki(x, y) of K'(x, y) coincides with the restriction of K to the set Ei, which completes our proof. The norm || ||i is especially simple when the subclass F0CF is reduced to the zero function. In this case F' = F, each function f G Fi is a restriction of one and only one function/G F (since every function of F vanishing in Ei vanishes identically everywhere in E), and therefore ||/i||i = ||/|| for the function / having the restriction /i. 6. Sum of reproducing kernels. Let K~i(x, y) and K2(x, y) be reproducing kernels corresponding to the classes Fi and F2 of functions defined in the same set E with the norms || ||i and || ||2 respectively. K~iand K2 are positive matrices, and obviously K = Ki-\-K2 is also a positive matrix. We shall now find the class F and the norm || || corresponding to K. Consider the Hilbert space § formed by all couples {/i, /2} with fiC.Fi. The metric in this space will be given by the equation
iiíA/.rir-ii/4!;+iwi5.
Consider the class F0 of functions/ belonging at the same time to Fi and F2 (F0 may be reduced to the zero function). Denote by §0 the set of all couples {/, —/} for/GF0. It is clear that §0 is a linear subspace of §. It is a closed subspace. In fact if {/„, —/»}—*{/',/"} then/„ converges strongly to /' in Fi, and —/„ converges strongly to f" in F2. Consequently,/„ converges in the ordinary sense to/' and —/„ to/", which means that/"= —/' and/' and/" belong to F0. Jpo being a closed linear subspace of § we can consider the complementary subspace §' so that ¿£>= §o®^>'- To every element of §: {/'>/"} there corresponds the function/(x) —f(x)+f"(x). This is obviously a linear correspondence transforming the space § into a linear class of functions F The elements of § which are transformed by this correspondence into the zero function are clearly the elements of §0- Consequently, this correspondence transforms §' in a one-to-one way into F. The inverse correspondence transforms every function/GF into an element [g'(f), g"(f) ] of §'. We define the metric in F by the equation
\W-\\{m,i'(î)}\t= h'(i)l+ h''U)\\l^
Our assertion will be that to the class F with the above-defined norm there corresponds the reproducing kernel K = K~i-\-K2. To prove this assertion we remark: (1) K(x, y) as a function of x, for y fixed, belongs to F Namely, it corresponds to the element [K~i(x, y), K2(x, y) ] G$(2) Denote for fixed y, K'(x, y)=g'(K(x, y)) and K"(x, y) =g"(K(x, y)). For a function/GF we write f =g'(f),f" = g"(f). Consequently, f(y) =f(y) +f"(y), K'(x, y)+K"(x, y) =K(x, y)=Ki(x, y)+K2(x, y), and thus K"(x, y) —K2(x,y) = - [K'(x,y)-Ki(x,y)], so that the element jKi(x, y) -K'(x, y),


 1950] THEORY OF REPRODUCING KERNELS 353
K2(x, y) -K"(x, y)} G£>o. Hence
/(y) = A(y) + /"(y) - (f (*), Ki(x, y))i + (f"(x), k2(x, y))2
= ({/',/"}, {Ki(x, y),K,(x, y)\)
= (i/',/"}. {K'(x,y),K"(x,y)\)
+ ({/',/"}. {KÁx, y) - K'(x, y), K2(x, y) - K"(x, y)\).
The last scalar product equals zero since the element {/', /"} G§' and the element {Ki(x, y)—K'(x, y), K2(x, y)—K"(x, y)}G£»o- The first scalar product in the last member is, by our definition, equal to (f(x), K(x, y)) which proves the reproducing property of the kernel K(x, y). We can characterize the class F as the class of all functions f(x) =fi(x) +f2(x) with fiQFi. In order to define the corresponding norm without passage through the auxiliary space, we consider for every/GFall possible decompositions/=/i+A with/E G £,. For each such decomposition we consider the sum ||/i||2i+ ||Á||2-ll/ll will then be defined by
|j/f- miI*M +¡WH]
for all the decompositions of /. To prove the equivalence of this definition and the previous one we have only to remember that f(x) corresponds to the element {/i, /2} G§ and also that/ corresponds to \g'(f), g"(f)} G§', that is,/=A+A = g'(/)+g"(/)- Consequently,
A -g"(f) = - [h-g'(f)]
so that {h-g'(f),fii-g"(f)} G£o and
IWI+ÎIWI=Î IliAAlir=II{?'(/s)."(f)}\+t II(A- im/, - g"(f)}\\\
and this expression will obviously get the minimal value if and only if fi-g'(f), h —g"(f) and its value is then given by
\\{g'U),g"U)}\\\
which by our previous definition is ||/||2. Summing up, we may write the following theorem:
Theorem. If Ki(x, y) is the reproducing kernel of the class Fi with the norm || i, then K(x, y) =Ki(x, y) +K2(x, y) is the reproducing kernel of the class F of all functions f=fi+f2 with fiQFi, and with the norm defined by
ll/ll2= min [\\fl\\\+ ||/2||22],
the minimum taken for all the decompositions f=fi+f2 with /¡G£»(6).
It is easy to see how this theorem can be extended to the case where
(6) This theorem was found by R. Godement [l] in the case of a positive definite function in a group.


 354 N. ARONSZAJN [May
K(x, y) = 23"-1 ^¿(-T> y)- A particularly simple case presents itself when the classes Fi and F2 have no function besides zero in common. The norm in F
is then givensimplyby ||/||HI/i|l? + K
In this case (and only in this case) Fi and F2 are complementary closed subspaces of F. If we denote by F the class of all conjugate functions of functions of a class F, then the kernel of F is clearly K~i(x, y) =K(x, y) =K(y, x) (K is the kernel of F and in F the scalar product (/, |)i is given by (g, f), the norm ||/||i by D/11). Consequently Re K(x, y)=2~x(K(x, y)+K(y, x)) is the reproducing kernel of the class F0 of all sums/+g, for/ and g in F with the norm given by
(1) ll^iu= 2min[U/H+2lUH2],
the minimum taken for all decompositions c6=/+!, / and g in F. If F is a complex space corresponding to a real space, that is, if F=F
and ll/ll=||/|| (see§l),it is clear that F0= F and ||/||o = |l/ll- Consequently the
kernel K = Re K is real and this property characterizes the kernal K corresponding to a real space. 7. Difference of reproducing kernels. For two positive matrices, Ki(x, y) and K(x, y), we shall write
1) Ki « K
if K(x, y)—Ki(x, y) is also a p. matrix. From Ki<£.K2<£K3, it follows clearly that Ki<£K3. On the other hand, if Ä'i«Ä"2 and K2<ZCKi,it follows that Kx = K2. In fact, we then have K2(x, x) —K~i(x, x) 3:0 and alsoKx(x, x)—K2(x, x) 3:0, which meansK2(x, x) —Ki(x, x) = 0. Further, by the property of positive matrices,
\K2(x, y) - Ki(x, y) |2 á [K2(x, x) - Ki(x, x)][K2(y, y) - Ki(y, y)] = 0,
so that K2(x, y) =R~i(x, y) for every x, y in E. Thus we see that the symbol <iC establishes a partial ordering in the class of all positive matrices.
Theorem I. // K and K~i are the r.k.'s of the classes F and Fi with the norms || ||, || ||i, and if K~i<ZK,then F1CF, and ||/i||i3:||/i|| for everyfiE.Fi.
Proof. A^i«AT means that K2(x, y) =K(x, y)—Kx(x, y) is a positive m"tr;x. Consider the class of functions F2 and the norm || ||2 corresponding to K2. As K = R~i+K2 we know by the theorem of §6 that F is the class of all functions of the form fi(x)+f2(x) with fiC.Fi and f2E.F2. In particular, when /2 = 0, the class F contains all functions f G Fi so that F¡C.F. On the other hand, in F we have, by the same theorem,
iwi'-»faiiwe+iwi'.]
for all decompositions/i =/i'+/2', with A' (EFi and fi EF2. In particular, for


 1950] THEORY OF REPRODUCING KERNELS 355
the decomposition A =A+0, we obtain
which achieves the proof.
Theorem II. If K is the r.k. of the class F with the norm \\ \\, and if the linear class FiCZF forms a Hubert space with the norm K, such that A i
II 11 Mil
= ||A|| for every fiQFi, then the class Fi possesses a reproducing kernel Ki satisfying Ki<^K.
Proof. The existence of the kernel for F involves the existence of constants Mv such that |/(y)| ^i^„||/|| for all fQF. In particular, forfiQFiQF', we get
|A(y)| áiif*||AlláJf,||/i||x
which proves the existence of the kernel Ki of Fi. Let us now introduce an operator L in the space F, transforming the space F into the space Fi and satisfying the equation
(A. /) = (A. Lf) i. for every /, £ Fu
The existence and unicity of Lf is proved in the following way: (A, /), for fixed/, is a linear continuous functional of A in the space F. A fortiori, it is a similar functional in the space Fi. As such, it is representable as a scalar product in Fi of A with a uniquely determined element Lf of Fi. The operator L is everywhere defined in F, linear, symmetric, positive, and bounded with a bound not greater than 1. It is clear that L is everywhere defined and linear. It is symmetric because for any two functions /, /' of F,
(Lf, f') = (Lf, Lf')i = (Lf, Lf)i= (Lf, f) = (/, Lf). It is positive because
(Lf,f) = (Lf, Z/)i§:0. It is bounded with a bound not greater than 1 because
(Lf,f) = (Lf, Lf)i= \\Lf\\\^\\Lf\\2.Consequently, \\Lf\\2^(Lf,f)^\\Lf\\-\\f\\,
and thus HL/1g1||/||.
Consider now the operator I —L (I being the identical operator). This operator clearly possesses the same properties as those enumerated above for L. Therefore there exists a symmetric, bounded square root L' of this operator. (In general there will be infinitely many L' available and we choose any one of them.) Hence L'2 = I - L.
We define F2 as the class of all functions f2 = L'f for fQF. Denote by F0 the closed linear subspace of F transformed by L' into 0, and by F' the complementary space F&F0. The functions of F0 are also characterized by the fact that Z'2/=0 (from Z/2/=0 it follows that (L'2f,f) = (L'f, L'f) =\\L'f\\2 = 0) which is equivalent to f=Lf. Now denote by P' the projection on F'. Every two functions /, g of F transformed by L' into the same function f2 of F2 differ by a function belong


 356 N. ARONSZAJN [May
ing to F0. Consequently, they have the same projection on F'. It is also clear that the class F' is transformed by L' on F2 in a one-to-one way. We remark further that F2CF
since for /oGF0, (/o, L'f) = (L'fa, f) = (0, /) =0. In the class F2 we introduce the norm || ||2 by the equation
II/2II=211*711, forany/withf2= L'f.
With this metric the class F2 is isometric to the subspace F'CF (the isometry being given by the transformation L'). It follows that F2 is a complete Hilbert space and we shall show that the class F2 with the norm || ||2 admits as reproducing kernel the difference K(x, y)—Ki(x, y). To this effect we remark firstly that the operator L is given by the formula
My) mLf- (f, Ki(x, y)).
In fact, since LfE.Fi, f(y) = (f(x), Ki(x, y))i=(f(x), Kx(x, y)). Consequently for any fixed z, the operator L applied to K(x, z) gives the function LK(x, z) =Ki(y, z). If follows that the operator I —L = L'2 transforms K(x, z) into L'2K(x, z) =K(y, z) —Ki(y, z). This formula proves, firstly, that K(x, z) —K~i(x, z) as a function of x belongs to F2, since it is the transform of L'K(x, z) by L'. Secondly, we prove the reproducing property for any f2EF2:
My) = (h(x), K(x, y)) = (L'f, K(x, y)) = (/, L'K(x, y))
= (P'f, P'L'K(x, y)) = (L'f, L'L'K(x, y))2
= (f2(x), K(x, y) - Ki(x, y))2.
In these transformations we took/ as any function of F such that f2 = L'f and we used the property L'K'x, y)GF2CF'. This finishes the proof of our theorem. The proof of Theorem II has established even more than the theorem announced: namely, it gives us the construction of the class F2 and the metric ||2 for which the difference K —K~i is the reproducing kernel. Let us summarize this in a separate theorem.
Theorem III. Under the hypotheses of Theorem II, the class F2 and the norm || ||2 corresponding to the kernel K2 = K —Ki are defined as follows: the equation fi(y) =Lf= (f(x), K~i(x, y))x defines in F a positive operator with bound not greater than 1, transforming F into FiCF We take any symmetric square root L'=(I—L)112. F2 is the class of all transforms L'f for f(EF. Let F0 be the closed linear subspace of all functions /G F with f=Lf and let F' be F-&F0. L' establishes a one-to-one correspondence between F' and F2. The norm \\f2\\2for f2= L'f, f'EF', is then given by


 1950] THEORY OF REPRODUCING KERNELS 357
The construction of the class F2 is somehow complicated because we need the square root L' of the operator I—L. However, there exists a much easier way of constructing an everywhere dense linear subclass of F2 and the norm |l ||2 in this subclass. Namely, we can consider the class F2 of all transforms (I-L)f=f-Lf=L'2f, of/GF by the operator I-L. This clearly is a linear subclass of F2. The norm || ||2 in Fi can be defined as follows:
II/ÍIÍ= l|£7|f= (L'f,L'f)= (/,£'7)= (/,/- Lf)- (/,/) - (/,Lf)
= (f,f)-(Lf,Lf)i.
In these transformations we considered// =/— Lf = L'*f. F2 is everywhere dense in F2 (in respect to the norm || ||2), otherwise we would have a function f2 = L'f ^0 with (L'f, L'2g)2= 0 for all gGF. We can suppose here/'GF' so that 0 = (£'/', L'2g)2=(f, L'g) = (L'f, g) whence L'/' = 0,/'GFo, which is impossible. The simplest case is the one where Fi = F2. By using the spectral decomposition, we can easily show that this case presents itself if, and only if, the zero is not a limit point of the spectrum of L', which is the equivalent of saying that 1 is not a limit point of the spectrum of L. In this case F2=F'. If L has a bound <1, the spectrum does not contain 1 and the subspace F' coincides with the whole space F so that F2 = F. When L is completely continuous, the only limit point of the spectrum of L is zero, so that 1 is certainly not a limit point, and Fi =F2 = F'. We shall add still another theorem which results immediately from Theorem III.
Theorem IV. Let K be the r.k. of class F. To every decomposition K = K\ +K2 in two p. matrices K~i and K2, there corresponds a decomposition of the identity operator I in F in two positive operators L\ and L2, I = L\-\-L2, given by
Lif(y) - (/(*), Ki(x, y)), L2f(y) = (f(x), K2(x, y)),
such that if Li and Z¿ denote any symmetric square roots of Li and L2, the classes Fi and F2 of all transforms L\/2fand Ll/2f respectively, /GF, correspond to the kernels Kxand K2. If F¿0,i = 1, 2, is the class of all /G F with Lif= 0, and if Fi' =FOF,o, then L\12 establishes a one-to-one correspondence between FI' and Fi and the norm || ||¿ in Fi is given by j|L¡ 2/||¿= 11/||for everyfEF¡'. Conversely, to each decomposition I = Li-\-L2 in two positive operators there correspond classes Fi with norms [| || ; defined as above. The corresponding r.k.'s K~iare defined by Ki(x, y)=LiK(x, y) and satisfy the equation K = Ki-\-K2.
8. Product of reproducing kernels. Consider two positive matrices Ki


 358 N. ARONSZAJN [May
and K2 defined in a set E. Using a classical result of I. Schur concerning finite matrices, it is easy to prove that their product Ki-K2 is also a positive matrix. We shall prove this theorem, constructing at the same time the class Fand the norm || || corresponding to the matrix K = Ki-K2C). To this effect, we consider the class £,• and the norm || ||t-corresponding to Ki and form the direct product F' of the Hubert spaces Fi and F2, F' = Fi®F2(s). We construct this direct product in the following manner: We form the product set E' = EXE of all couples of points {xi, x¡¡¡, x.G-E. In the set E' consider the class of all functions f'(x\, x2) representable in the form:
(1) f(xi, x2)= Z/i (*i)A (*0i
4=1
with /i G Fi and ffi QF2. As scalar product of two such functions we define:
(2) (/', g')' = ¿¿(/i , gi )i(A i gi )»•
k=l 1=1
where m is the number of terms in the representation of g'. The same function/' may admit of many different representations of type (1). The scalar product, (/', g')', is independent of the particular representation chosen for /' and g'. In fact, we see immediately from (2) that
(3) (/', g'Y = Z ((f'(xi, x2), gi\xi))h g[l\x))2
i=i
which proves that (/', g') is independent of the particular representation of/'. In a similar way we prove that it is independent of the particular representation of g'. We still have to prove that (/', g')' satisfies all the requirements for the scalar product. It is clearly seen that it is a bilinear hermitian form in /', g' and it remains to be proved that (/', /')'^0 and is equal to zero only when /' = 0. In order to prove this, we take any representation of /' of type (1) and orthonormalize the sequences {A(t)} and {f^} in the spaces Fi and F2 respectively. Denote by {/Í*'15} and {/i!,1)} the orthonormalized sequences, where k=i, 2, • • • , «i, /= 1, 2, • • • , n2. Every function ff* is then a linear combination of the orthonormal functions fi A' so that we obtain a representation for /' as a double series
(4) f(xi, x2)= ZZ«*.iA A •
We then obtain for (/',/')' the following expression
(7) The idea of the proof was arrived at independently by R. Godement and the author. Godement applied it only to positive definite functions. (8) For the notion of direct product of abstract Hubert spaces see J. v. Neumann and F. J. Murray [l].


 1950] THEORY OF REPRODUCING KERNELS 359
te t>\ v1 v v v - c/*'1' /^N r/u,1) /''4\
(/./) = 2^2^ 2^ ¿uak.iak',i'(fi ,A )i (A ,A )s
*-i i-i *'=i í'=i
= ZZI«*.<I2
*=1 Í-1
It is clear from this representation that (/',/') Ïï0 and equals zero only when all the ock,i= 0, that is, when/' = 0. The class of all functions/' of type (1) does not yet form in general a Hubert space because it may not be complete. To complete this class with respect to the norm || ||', we consider a complete orthonormal sequence {gf^} in the space Fi, i=l, 2. It is obvious that the double sequence {^'(x,) -gffa)} is composed of functions of type (1) and is orthonormal in respect to the norm || ||'. Consider then, all the functions g' of the form
(6) g'(xu x2) = Z Z otk.igi (xi)g2 (x2)
k=l 1=1
with
(7) (§',«T = í:í:i«ui!<».
k=l 1=1
It is clear that any finite sum of type (6) is also of type (1) and that the norm || ||' for such finite sums coincides with the norm introduced in (7). We prove firstly that every sum of type (6) is absolutely convergent for every xi, x2. In fact, as the class Fi possesses the reproducing kernel K\, in view of (7) we have
Z|a*,¡||A*i)|^ [*i(*i,*i)H"è|«*.«|,ï
[oo -11/2
ZI
4=1
Then,
V1 V1! II wr ^ I I iv>t \ I
2^ 2J a",i\ | gi (xi) \ | g2 (x2) |
k=l 1=1
(8) ^ ¿Z\g*\x2)\[Ki(xi,*0]1/sr¿I «*.il*T
i=i l_*-i J
[Ki(xi,Xi)Y'2[K2(xx2,2)]i'2.[ Z Z I«*.«I2l
L k=i i=i J
1/2
since the space F2 possesses the reproducing kernel K2. The class of functions g' of the form (6) clearly forms a complete Hilbert space, isomorphic with the space of double sequences {a*,:} satisfying (7). The inequality (8) gives us further, for a function g' of type (6),


 360 N. ARONSZAJN [May
I g'(yi, y2) | < Ki(yi, y1)I'2A'2(y2, y2Y'2\\g'\\',
which means that the space of functions of type (6) possesses a reproducing kernel. It remains to be proved that this space is the completion of the class of all functions/' of type (1) with the norm || ||'. As already the finite sums of type (6) are everywhere dense in the space of all functions of type (6) it is sufficient to prove that every function of type (1) is of type (6). For this, it is enough to prove that every function of type (1) may be approximated as closely as we wish (in respect to the norm || ||') by finite sums of type (6). Let us consider a representation (1) of the function/'. We can approximate every f^ by a finite linear combination hf* of functions g® so that [|AÍ*Jj|» = ll/iW|l'-. ||/í(i°-^(i;)||¿=~í- Before we proceed further, we shall prove for every function/' and any of its representations (1) the inequality
In fact,
rlNZII/Hlfll/ril,
'■-(rJT-EEÄAiCtfU0).
íZri^lMlyínIK-imi.ll/.,,ll.
t=ii=i
- TvH^'ll II/*'!T!
- 2-v 11/1 ||l||/2 l|2
L k=l
Continuing with the proof of the approximation we consider the functions
h'(xu x2) = 23 *i (xi)f2 (x2),
k—i
g'(xh x2) = 23 ¿i (xi)h2 (x2).
k—l
It is clear that h' is of type (1) and that g' is at the same time of type (1) and (6), which can be seen by developing the functions hf^ as linear combinations of gj°. Denoting by M the maximum of all H/j^Ht, we obtain
\\f-gf^\\f-h'\\' + \\h'-g'\\',
\\f - h'W= ±\\(f[k\xi) - h[k)(xi))Ak\x2)\\'
k=l
áefl/f'-AÍlrllAá ±Me=nM(,


 1950] THEORY OF REPRODUCING KERNELS 361
Z ¿i (xi)((/2 (x2) - h2 (x2))
h
k=l
(*)ii M „(*) ,<*)l|
^Zll*i ||x-||/iK-hr\\2^¿ZM,= nMe.
k-l k=l
Finally, we obtain
||/' - g'll' á 2nMe,
which proves our assertion. The class of all functions of type (6) with the norm given by (7) forms the direct product F' —Fi®F2. As it is obtained by functional completion of the class of functions of type (1), this class being independent of the choice of orthogonal systems {gi*1} and {g*}. the class F' is also independent of the choice of these systems (see the uniqueness of functional completion in §4). We shall now prove the following theorem:
Theorem I. The direct product F' = Fi®F2 possesses the reproducing kernel K'(xi, x2, y\, y2)=Ki(xi, yi)K2(x2, y2).
The proof is immediate. Firstly, as a function of X\, x2, K' is of the form (1) and so belongs to F'. Secondly, for any function g' of the form (6) we have
g'iyu yt) = Z Z «*.i(gi (xi), Ki(xi, yi))i(g2 (x2), K2(x2, y2))2
= (g'(xi, x2), K'(xi, x2, yi, y,))'
which completes the proof. From Theorem I we see immediately that the kernel K(x, y) = Ki(x, y)K2(x, y) is a p. matrix as the restriction of the kernel K'(xi, x2, yi, y2) to the subset EiQE' consisting of the "diagonal" elements {x, x\ of E'. Further, from the theorem of §5 we obtain the class of functions and the norm corresponding to the kernel K. Thus we have the following theorem.
Theorem II. The kernel K(x, y) =K~i(x, y)K2(x, y) is the reproducing kernel of the class F of the restrictions of all functions of the direct product F' = Fi® F2 to the diagonal set Ei formed by all the elements \x, x\ QE'. For any such restriction f, ll/ll =min ||g'||'/0r all g'QF', the restriction of which to the diagonal set Ei is f.
Remark. Let {g?} be a complete orthonormal system in Fj. Then every function fQF is representable as a series
f(x) = ZA (x)gi (x),f2 QF2, 2^||A II2< ».
Among all such representations of /(x) there exists one (and only one)


 362 N. ARONSZAJN [May
which gives its minimum to the sum 23||/*)||2:- This minimum is equal to ||/||2. We can apply Theorem II to a class F and its conjugate F. The product of the corresponding kernels is |K(x, y)\2 = K(x, y)K(y, x) and the corresponding class may be obtained from the remark above. 9. Limits of reproducing kernels. We shall consider two cases: (A) essentially, the case of a decreasing sequence of classes FOFO ■ • • with a decreasing sequence of kernels K{5>K2^>K3^> • • • ; (B) essentially, the case of an increasing sequence of classes and kernels. A. The case of a decreasing sequence. Let {En} be an increasing sequence of sets, E their sum
(1) E = Ei + E2 + ■■• , Ei C £2 C • • • •
Let F„, n = 1, 2, • • -, be a class of functions defined in En. For a function /nGFn we shall denote by/„m, m^n, the restriction of/„ to the set Em(ZEn (fnn=fn)- We shall suppose then that the classes F„ form a decreasing sequence in the sense
(2) for every fn G Fn and every m g n, fnm G Fm.
Suppose further that the norms || ||„ defined in Fn form an increasing sequence in the sense
(3) for every /„ G Fn and every m g n, ||/nm|| m g ||/„||„.
Finally, we suppose that every F„ possesses a reproducing kernel Kn(x, y). The case of all sets En equal, Ei = E2= ■ ■ ■ = E, is not excluded. Clearly, in this case/„„,=/„, Fn(ZFm, and, following Theorem II of §7, it is enough to suppose the existence of R~i(x, y) in order to deduce the existence of all Kn and to obtain the property Kn<^Km for m<n. In the general case we have to introduce the restrictions Knm of Kn to the set Em (m^n). By the theorem of §5, Knm is the r.k. of the class F„m of all restrictions/„,,, for/„GF„. The norm in Fnm is given by
||/»m||nm = min ||/á||„ for all f'n with fnm = fnm.
From (3) we get
||/nm|j7im = ||/7tm||îîi
and consequently, by Theorem II of §7,
(4) Knm « Km, m < n.
We shall now prove the following theorem.
Theorem I. Under the above assumptions on the classes Fn, the kernels Kn converge to a kernel K0(x, y) defined for all x, y in E. Ko is the r.k. of the class F0 of all functions /0 defined in E such that Io their restrictions f0n in En


 1950] THEORY OF REPRODUCING KERNELS 363
belong to Fn, n=l, 2, ■ ■ • , 2° limn=00 ||/on||„< «. The norm of /0G£o is given
by ||/o||o = lim„=M ||/on||n.
Remark. Condition Io implies, following (3), that limn=00||/o„||„ exists, but it may be infinite. Proof. The convergence of Kn to K is to be understood in this way : any two points x, y in £ belong to all £„ starting from some £„0 on. Consequently Kn(x, y) are defined for n>no and we have to prove lim„=00 Kn(x, y) =K(x, y). For fixed yQEk and k^m^n we have, following our assumptions,
\\Kmh(x, y) — Knh(x, y)\\k S \\Km(x, y) — Knm(x, y)\\n
= Km(y, y) - Knm(y, y) - Knm(y, y) + \\Knm(x, y)\\m
g Km(y, y) - 2Kn(y, y) + \\Kn(x, y)\\l
= Km(y, y) — Kn(y, y).
From (4) it follows that Km —Knm is a p.d. matrix. Therefore Km(y, y) — Knm(y, y)=Km(y, y)—Kn(y, y)^0, and the sequence [Km(y, y)}m^k is a decreasing sequence of non-negative numbers. Consequently it is a convergent sequence. (5) shows then that the functions Kmk(x, y)QFk, for fixed k and m—>*>, converge strongly in Fk to some function <pk(x)QFk. This involves limm=0O Kmk(x, y)=limm=00 Km(x, y)=<pk(x) for every xG£*. Since for every x, y in £ we can choose a k so that x and y belong to Ek, it is clear that Km(x, y) converge and that the limit K0(x, y) does not depend upon the choice of k. The function qt>k(x)is clearly the restriction K0k(x, y) of Ko to Ek. Consequently Kmk(x, y), for fixed y, converges strongly in Fk to Kok(x, y) which belongs to Fk. We then obtain from (5), by taking n—>»,
(6) \\Kmk(x, y) - K0k(x, y)\\\ á K„(y, y) - K0(y, y):
\\Kok(x, y)\\k è \\Kok(x, y) — Kmk(x, y)\\k + \\Kmk(x, y)\\k
è (Km(y, y) - K0(y, y))1'2 + \\Km(x, y)\\m
^ (Km(y, y) - Ko(y, y))1'2 + (Km(y, y))1'2
and for ra—>«>, ||i2;oi(x, y)||i^ü:o(y, y). Therefore for each yQE, K0(x, y), as function of x, belongs to the class F0 of our theorem. Let us now prove that the class £o is a Hubert space. £0 is linear, since ||a/o„+|ögo*||na |«| ||/o»||n+|ß| ||go»||n. ||/o||o is a quadratic form, since
\\afo + ßgo\\o = Hm \\afon + ßg0n\\n n= «o
= Km [aä||/o„||n + aß(fon, gOn)n + äß(g0n, fon)n + ^||«0n||n].


 364 N. ARONSZAJN [May
Since the quadratic form in square brackets converges for all values of the complex variables a, ß, it converges to a form of the same kind. This proves that ||/o||o is a quadratic form and also that
(7) (/o, go)o = Hm (fon, gOn)n.
n= m
It remains to be proved that F0 is complete. Take a Cauchy sequence {fon)}C.F0. The inequality ||/cï}— /ä'||* £W-j8\\i, for l>k, gives, when i-co, \\f0f-jV\\k^\\fom'~fon)\\o- Hence, {fok \m=i,2,... is a Cauchy sequence in Fk, Hmm=00/o*1>='/'a-GF*. It is clear that \pk is the restriction to E* of a function \p0 defined in E. We have
\\fok — fakWk= Hm ||/o* —/o* ||* á lim ||/0 —f0" \\o.
n=oo n— »
This allows us to prove that i/'oG F0, since it gives a bound for H^o*'!* independent of k, namely
WMgUii/ór'i+u Hmii/a"-"/on,i^iou/.!.+hm n/r - /;%
n= oa n= oo
On the other hand, it shows that
H/oTM— ^o||o = hm ||/or — ^o*||* S=lim ||/0m —f0" ||o
k= « n= oo
and consequently limm=100||/om)—^o||o = 0. This achieves the proof of completeness. We have still to prove the reproducing property of K0. To this effect take any/oGFo, yG-E- For sufficiently large n we have
fo(y) = fon(y) = (fon(x), Kn(x, y))„ = (fon(x), K0n(x, y))„
+ (fon(x), Kn(x, y) — Kon(x, y))n.
For n—*oo, the first scalar product in the last member converges, by formula (7), to (/0, K0(x, y))o- The second scalar product converges to 0; in fact, by formula (6) (with k = m = n), it is in absolute value smaller than
\\fon\\nKn(x, y) - Kon(x, y)\\n ^ \\fo\\o(Kn(y, y) - K0(y, y))1'2.
This achieves the proof of our theorem. B. The case of an increasing sequence. Let {En} be a decreasing sequence of sets, E their intersection
(8) E=Ei-E2-, FOFO---.
Let F„ be a class of functions defined in En. As before, we define the restriction fnm, for/„GFn, but now m has to be greater than n. We suppose then that F„ form an increasing sequence


 1950] THEORY OF REPRODUCING KERNELS 365
(9) for every fn G Fn and every m ^ n, fnm G Fm.
We suppose further that the norms || ||„ form a decreasing sequence
(10) for every fn Q Fn and every m }Z n, ||/„m||m á ||/„||n.
Finally, we suppose that every F„ possesses a r.k. Kn(x, y). Now, even for all £„ equal, we cannot deduce the existence of all kernels Kn from the existence of one of them. As in the case A, we get for the restrictions Knm of Kn the formula
(11) Knm « Km, for m> n.
For yQE, {Km(y, y)} is an increasing sequence of positive numbers. Its limit may be infinite. We define, consequently,
(12) £0 = set of y G E, such that K0(y, y) = lim Km(y, y) < ».
m= »
For an illustration of this point consider Bergman's kernels Kn for a decreasing sequence of domains £„. If the intersection £ of the domains £„ is composed of a closed circle with an exterior segment attached to it, the set £0 will be composed of all interior points of the circle. We suppose that £0 is not empty and define the limit-class of the classes Fn in the following way: let F0 be the class of all restrictions/n0 of functions fnQFn (n = i, 2, • • • ) to the set E0. From (10), we know that the sequence {[|/ni||k} *-«,n+i, ••• is decreasing and we can define
(13) ||/-o||o = lim||A*||».
As in case A we prove that ||/no||o is a positive quadratic form. This form is positive definite since from ||/„o||o = 0 it follows that for any yG£o, |/no(y) | = \U(y)\ = I(fnk(x), Kk(x, y))k\ ^\\fnk\\k(Kk(y, y))»MI/»o||o(#o(y, y))l/2 = 0, that is,/„o = 0. Consequently || ||0 is a norm in F0. In general F0 will not be complete. In order that F0 admit of a functional completion with a reproducing kernel, there are two conditions to be fulfilled which are given in the theorem of §4. The first one is that for every y there exists a constant My so that
(14) | Ao(y) | ^ Jf „||/»o||o for all fo G FB.
Let us remark that the functions fn0 may be considered as defined in the whole set £ (taking the restriction of /„ to £). Then, for every yQE, the condition (14) is equivalent to K0(y, y) =lim Kn(y, y) < ». In fact, from the latter condition it follows in the same manner as above that |/„o(y) | ^\\fno\\o(Ko(y, y)yi2, that is, (14) with My=(K0(y, y))1'2. From (14), by taking fn(x)=Kn(x, y) we get Kn(y, y)£My\\Kn0(x, y)\\oSMy\\Kn(x, y)||„ = My(Kn (y, y))1'2, that is, Kn(y, y)^M2y.


 366 N. ARONSZAJN [May
Consequently, condition (14), that is-,condition Io of §4, is assured by our restriction to the set Eo- But the condition 2° of §4 is in general not assured. We may illustrate this by the counter-example of §4. Take all the En equal to the set E of this counter-example. As class F„ we take the «-dimensional subspace of the class F introduced there, consisting of all polynomials of degree ^n. Each F„ is a complete space and its r.k. Kn converges to the Bergman kernel of the circle, restricted to E. Consequently E0 = E, F0 = F and || || o is clearly the norm introduced there. To overcome this difficulty we can proceed as indicated in §4. We complete F0 by ideal elements; in the completed Hilbert space F0 we choose an additional set E' of ideal elements such that the functions of F0, extended to Eo-\-E', with the same norm as in Fo, form a space admitting a functional completion leading to a class Fo with a reproducing kernel Ko. Following the theorem of §5, we can return now to our set Fo by restricting the functions of F0 to Fo- If we take in the restricted class the norm defined in the theorem of §5, we shall get as r.k. the restriction of Ko to Fo. The restricted class F0*and its norm || ||* can then be described, in terms of the space F0 and its norm || ||0, in the following way. /*GFo* if there is a Cauchy sequence {/o°} CF0 such that
(15) fo(x) = lim/o (x) for every x E Eo,
n= oo
(16) ||/o(*)||o = min lim ||/0n ||0,
n= »
the minimum being taken for all Cauchy sequences {/ón)}CFo satisfying (15). There exists at least one Cauchy sequence for which the minimum is attained. Such sequences will be called determining fo*. ■The scalar product corresponding to || ||* is defined by
(17) (fo, go)o = hm (fo , go )o
n= oo
for any two Cauchy sequences {/$"'} and {g0n^} determining /0* and go*. It is important to note that formula (17) is still valid when only one of the sequences {/o0}, {go"*} is determining, the other satisfying only (15). All these facts about the space F0* and its norm and scalar product are easily obtained when we form, as in §5, the subspace FqCFo of all/oGF0 vanishing in F0. The complementary subspace F0' =Fo-0-Fo is then in an isomorphic correspondence with F0*, Jó —>/o*,where /0* is the restriction of fó to Fo- Further,
\\]o\\o = ||/o||o, (fo, go)o = (fo, go)o,


 1950] THEORY OF REPRODUCING KERNELS 367
where || ||0 and ( , )0 are the norm and scalar product in F0. A Cauchy sequence {/£} C£o converges in F0 to a function j0. In the set £0 it converges everywhere to a function /0* G £o* which is the restriction of /o to £0. /o* is also the restriction of jó = projection of /o on Pó ■Since fo~fa G Fi we get
iimha:=ii/oii"=il/on:2+ha- /dir2^ ii/cîiir.
n=oo
The equality here is attained if {/on)} converges in F0 to/0'. Such a Cauchy sequence we have called as determining /0*. If now two Cauchy sequences {/o0} and {go*} converge everywhere in £0 to A* and go*, they converge in Fo to vectors /0 and |0 whose restrictions to £0 are/0* and g0*. If jó and go' are projections of j0 and |0 on F¿, then (/0*, go*)o*= (jó , gó )<T.but lim (jf\ gon))0 = (/o. go)o • If one of the sequences, say {/o }, determines its limit in £o, then/„=/„', and (A*, go*)o=*(/<>', go')o~= (fci, fo)o~= limCfT, goB))o. The space F0* being completely defined we prove the following theorem.
Theorem II. The restrictions Kno(x, y) for every fixed yQE0form a Cauchy sequence in F0. They converge to a function K0*(x, y)QFo* which is the reproducing kernel of F0*.
Proof. By an argument similar to the one used in (5) we obtain for n^m^k
(18) \\Kmk(x, y) - Knk(x, y)\\l Ú Km(y, y) - Kn(y, y).
Taking k—>» , we have
(19) \\Kmo(x, y) - Kno(x, y)||o Ú Km(y, y) - Kn(y, y).
This proves, together with (12), that {i£n0(x, y)} is a Cauchy sequence in F0. By property (14) this sequence converges for every xG£o to a function K*(x, y) which, by definition (15), belongs to F*. It remains to prove the reproducing property of K*. To this effect take any foQF* and a Cauchy sequence {/ón)}CF0 determining /*. Each /o0 is a restriction of someA-„GFin, /o")==A„o- By (13) there exists an increasing sequence mi<m2< • • ■such that
(20) mn > kn, ||A„mJ|L - ||A„o||o^ — •
n
It is clear that {i^m„o(x, y)} is also a Cauchy sequence converging to K*(x, y). Consequently, from (17) it follows that
(21) (/*(*), K*(x, y))0* = lim (fk„o(x), Kmno(x, y))0.
n— »
We may now write


 368 N. ARONSZAJN [May
(fk„o(x), Km„o(x, y))o = (/*„»„(«), Kmn(x, y))mn
(22) - [(/W*). ^«.(*. y))mn - (fkno(x), Kmno(x, y))o].
The square bracket is of the form [(g, h)mn—(g0, ho)o] for g, h of Fmn (go, h0 are restrictions of g, h to Fo). This is a bilinear form in g, h and the corresponding quadratic form (g, g)m„—(go, go)o = \\g\\mn — \\go\\l is positive (following (10) and (13)). Consequently the Cauchy-Schwarz inequality is valid for this form and in the case of the square bracket of (22) it gives in connection with (20)
11••«IIá niA*lf--.llAJßffllW*y)\\l- \\k~Ayx),\\l]m
^ - \\Kmn(x, y)|U„ = - Kmn(y, yY'2.
nn
For n—»oo this converges to 0, since Kmn(y, y)/Ko(y, y) < «>. Therefore, (21) and (22) yield
(fo(x), Ko(x, y))0 = lim (fknmn(x), Kmn(x, y))mn = lim/*„m„(y) n=oo n=oo
= lim/*„o(y) = lim/o" (y) = /*(y),
which is the reproducing property of K*. Remark. A particularly simple case is the one where the class F0 with the norm || || o happens to be a subspace of a class F possessing a reproducing kernel. Then, condition 2° of §4 is clearly satisfied; F* is the functional completion of F0, the norm || ||* is an extension of the norm |] ||0, and F* is simply the closure in F of F0. A trivial case of this kind is one where the Fn form an increasing sequence of subspaces of a class F with a r.k. Hence Ei = E2= • • • =F = Fo and F0* is the closure of the sum 23^»10. Construction of a r.k. by resolution of identity. Let us give a brief résumé of the essential properties of resolutions of identity in a Hubert space § (for a complete study of resolutions of identity, especially in connection with the theory of operators, see M. H. Stone [l]). For simplicity's sake we shall suppose here that the space £> is separable. We call a resolution of identity a class {P\} of projections in §, depending on a real parameter X, — oo <X< + oo, and having the following properties: 1. P\ is a projection on a closed subspace §\G§, increasing with X: £x'C£xforX'<X. 2. P\—>0 for X—>—oo ; Fx—>/ (identity operator) for X—>-f oo. For any open interval A: X' <X <X", we define
(1) A§ = £x»e<px', AF = Px- - Px<.


 1950] THEORY OF REPRODUCING KERNELS 369
AP is the projection on A^>. For any decomposition of the real axis into intervals Ak=(kk, As.+i), — »«—••• <A_2<A-i<Ao<Ai<A2< • • • —*+ », we have, obviously,
(2) I = Z A*F,
k
the series converging in the sense of strong limit for operators. A real number X0 belongs to the spectrum of {P\} if APy^O for every interval A containing X0. The numbers belonging to the spectrum form a closed set. For any real 9 and any decreasing sequence of intervals A„ containing 6 and converging to 9 there exist the limits
(3) beP = lim A„P, ôe& = lim A„§,
the second limit being the intersection of the decreasing sequence of subspaces A„§. These limits do not depend on the choice of A„ and b¡P is the projection on 5e¡£>.Only for an enumerable set of 9, say [9k], is ô^P^O. If we have 5enP = I, which means ¿>«1§+ ôjj§+ •••=§, we say that the spectrum of \P\] is discrete. If, for all 9, 5eP = 0, we say that the spectrum of {P} is continuous (often called purely continuous). In our applications we shall meet, essentially, only discrete spectra or continuous spectra. It has been proved (theorem of Hellinger-Hahn) that for any spectrum there exist finite or infinite systems {/n(X)} of elements /„(A) G £>, depending on X, such that if we denote by A/„ the difference/„(X") —/n(X'), we have (a) for my^n, (Aifm, A2/„) =0 for any intervals Au A2. (b) (Ai/„, A2fn) = 0 for any non-overlapping intervals Ai, A2. (c) For every interval A, the elements Ai/„, n = 1, 2, • • • for all AiCA, belong to the subspace A!q and form a complete system in A§. The minimal number of elements in such a system {/„(X)} is called the multiplicity of the spectrum. The spectrum is called simple if the multiplicity = 1, that is, if there exists such a system with only one element A(X). In the case of a discrete spectrum the multiplicity is the maximal dimension of the subspaces 5s§. If a system of elements {/n(X)} satisfies (a) and (b) and instead of (c) satisfies the weaker condition (c') The elements Afn for n =1,2, • • • and for all intervals A form a complete system in §, then the system {A(X)} determines a corresponding resolution of identity {P\} (for which it satisfies (c)) in the following manner:
§x is the subspace generated by all the A/n, n—1, 2, • • • , A = (X', X") with
X"<X.


 370 N. ARONSZAJN [May
This resolution of identity is continuous to the left, that is, ¿px= lim §x' for X'/'X. This condition (or the right side continuity) is usually accepted, for reasons of convenience, as an additional condition on resolutions of identity. For any system {/„(X)} satisfying (a), (b), and (c), it is seen that ||/n(X)||2 is a non-decreasing function /¿n(X), A/ín = ¿t„(X") —¿i„(X') = ||A/„||2. We consider the measure ¿u„, introduced on the real axis by Mn(X), which leads to the Lebesgue-Stieltjes integral /$(X)¿ju„(X). It has been proved that for every «G§ there exists the limit
... wx, .. («,A/») d(u,fn(\))
v/\, x"\x ||A/„||2 dpn(\)
for all X with exception of a set of /¿„-measure 0. We have further
(5) N|2 = 23 f°°|ç4„(x)l2^n.
n J —oo
(6) (u, v) = 23 I <bn(\)^n(^)dpn, where \pn(\) =
n •/ —oo
d(o, /.(X))
dp„(\)
Let us now apply the above considerations to the construction of a r.k. We suppose that our Hubert space § is a class of functions defined in E with a r.k. K(x, y). For a given resolution of identity {P\ ] every subspace A§ will have a r.k. which we shall denote by AK(x, y). The kernel AK determines the projection AP by the equation
(7) AP/ = fi(y) = (f(x), AK(x, y)), for any f G ©.
The kernel K corresponds to the identity / and following (2) we have
(8) K(x, y) = 23 à„K(x, y),
*
for any decomposition {A*} of the real axis. The series in (8) converges absolutely. In fact, following (2), the series K(y, z)=IK(y, z) = ~^AkPK(y, z) = ^2(K(x, z), AhK(x, y))x= ^,AkK(y, z) as function of y is strongly convergent. It converges then in the ordinary sense for every y, in particular for y = z. Thus, K(z, z) = ~YjAkK(z,z) < oo, AkK(z, z) 3:0. Consequently
£ | AkK(x, y) | S E (AkK(x, x)Y'2(AkK(y, y)Y'2
=S[23AaF(*, x)-ZàkK(y, y)]1'2.
If the resolution of identity {P\} has a discrete spectrum {0*} and if the r.k. of ôek& is denoted by öekK, then we have again an absolutely convergent representation


 1950] THEORY OF REPRODUCING KERNELS 371
(9) K(x, y) = Z KK(x, y).
k
An especially important case which is most often applied is one where the spectrum is simple. Then the subspaces ôek$Qare one-dimensional and each is generated by a function g*(x) which we can suppose normalized, ||g*||=l. The functions g&(x) form a complete orthonormal system in §. The kernels 8ekK(x, y) are given by gk(x)gk(y), and (9) takes the form of the well known development of the kernel in an orthonormal complete system
(10) K(x,y) = J^gk(x)ikJy),
k
which for a long time was taken as a basis of the definition of a r.k. Suppose now that the resolution of identity {P\} is given by a system of functions A(X)=/n(x, X) satisfying (a), (b), and (c'). Following (4) we define for u = K(x, y) (considered as function of x), the functions
„«, Ä, x, ,. (K(x,y),Afn) My, X") - fn(y, X') dfn(y,A)
(11) $n(y, A) = lim-= lim-= -• A~X Apn P-nW) — AU(A') ¿/¿n(A)
From (6) and (5) we then obtain
(12) K(y, z) = (K(x, z), K(x, y)) = Z f *»(y, \)Mz~X)dpn,
(13) K(y,y)= Z f I*.(y,X)1*4*..
The series and the integrals in (12) are absolutely convergent because of
(13). The function $n(y, X) is in general defined for each y only almost everywhere in X in the sense of the measure pn- Nevertheless, in most applications it turns out to be a continuous function of X. In spite of this, ^»(y, Xo), as function of y for a fixed X0, will not in general belong to §. 11. Operators in spaces with reproducing kernels(9). In a class F forming a Hubert space with a r.k. K, the bounded operators admit of an interesting representation. The notation LxK(x, y) indicates that the operator is applied to K(x, y) as function of x and that the resulting function is considered as function of x (but it will depend also on y which will act in the transformation as a parameter). It is then clear what is meant by LzK(x, z), LxL'zK(x, z), and so on. The notation Lf(x) is clear and we may also write Lf(x0) if xo is a particular value of x. Consider the adjoint operator!,* (that is, the operator for which (Lf, g) = (/, L*g)). Take the transform
(9) The developments of this section are closely related with the work and ideas of E. H. Moore.


 372 N. ARONSZAJN [May
(1) A(x, y) = L*xK(x, y).
A is a function of the two points x, y. As function of x it belongs to F. Take then for any/GF the scalar product (f(x), A(x, y))x= (f(x), L*K(x, y))x = (Lf(x),K(x,y))x = Lf(y),
(2) Lf(y) = (f(x), A(x, y)).
In this way, to each bounded operator there corresponds a kernel A(x, y) which for every y, as function of x, belongs to F The operator is represented in terms of the kernel by formula (2). Let us now find the kernel A*(x, y) corresponding to the adjoint operator L*. We have (L*)* = L and thus
(LxK(x, z), K(x, y)) = (K(x, z), L*xK(x, y)),
(A*(x, z), K(x, y)) = (A(x, y), K(x, z)),
(3) A*(y, z) = A(z, y).
It is clear that to Li-\-L2 or aL correspond Ai+A2 and aA respectively. We shall now find the kernel A corresponding to the composition L = L\L2. Since (Li L2)* = L*L*, we have
A(y, z) = (LiL2)yK(y, z) = L2yLiyK(y, z)
= F2„Ai(y, z) = (A^x, s), A2(x, y)) = (Ai(x, z), A2(y, x))
(4) A(y, z) = (Ai(x, z), A2(y, x)) for L = LiL
Let us note the following properties resulting immediately from (l)-(4)
((/(*), A(x, y))x, g(y))y = (/(*), (g(y), A(x, y))y)x
- (f(x),(A(x,y),g(y))y)x.
(6) The symmetry of L is equivalent to the hermitian symmetry of A :
A(x, y) = A(y, x).
We prove now the following property :
(7) The operator L is positive if and only if A is a p. matrix.
In fact, L positive means that for every fEF, (Lf, /)3r0. For /= ^nitkK(x, yk) we then get
2323Çih(L*K(yxi,),K(x,y¡))
ii = E 23Üi(A*(xy,i),K(x,y,))= 2323A*(y,y-,,)Mi = 2323A(y,y-,^if i > 0.


 1950] THEORY OF REPRODUCING KERNELS 373
This proves that A and thus A is also a p. matrix. It also proves the well known fact that a positive operator is always symmetric. If now A is a p. matrix, we see that (Lf, f) =50 will be satisfied for all / of the form Z"f*-^(-T> yk). As these functions form a dense set in F, every function fQF may be approximated by them and we get (Lf, /)^0 by a passage to the limit. In generalizing the notation of §7 we shall write Ai<<CA2or A2<3CAfior any two kernels if A2—Ai is a p. matrix.
Theorem I. For an arbitrary kernel A(x, y), hermitian symmetric (that is, A(x, y) =A(y, x)), the necessary and sufficient condition that it correspond to a bounded symmetric operator with lower bound =îm > — » and upper bound g,M< + » is that mK«A«.MK.
Proof. Necessity. If L is the corresponding symmetric operator with bounds not less than m and not greater than M, we have
m(f, f) ^ (Lf, f) g M(f, f) for every/ G F.
It follows that ((L-mI)f,f)^0 and ((MI-L)f,f)^0, that is, the operators L —ml and MI —L are positive. Therefore, from (7) we obtain that A —mK and MK—A are p. matrices. Sufficiency. The condition of the theorem is clearly equivalent to
1
0 «-(A - mK) « K.
M —m
This means that the kernel Ki = (l/(M—m)(A —mK) is a p. matrix and is <Crv. Therefore it is a reproducing kernel of a class Fi with the norm || ||i and following Theorem I, §7, FiCF and ||/i||j ^||/i|| for/iGFi. Then, as in Theorem III, §7, the operator
Lif(y) = (f(x), Ki(x, y))
is a positive operator in F with a bound not greater than 1, that is,
0â(W,/) á (/,/)•
This operator corresponds to Ä"i(x, y) by its definition. Consequently, to A= (M —m)Ki+mK there corresponds the operator L= (M—m)Li+mI and the last inequalities give
m(f,f) :g (miff) + ((M- m)Lif,f)k M(f,f), m(f,f)ú(Lf,f)ÚM(f,f).
An arbitrary kernel A is representable in a unique way in the form
(8) A = Ai + iK2, Ai and A2 hermitian symmetric.
Namely, we have


 374 N. ARONSZAJN [May
1_
Ai(x, y) = — (A(x, y) + A(y, x)),
As(z, y) = — (A(x, y) - A(y, x)).
2i
The necessary and sufficient condition in order that A correspond to a bounded operator is, clearly, that Ai and A2 correspond to such operators. To the last kernels we can apply Theorem I. We now consider convergence of operators. The three simplest notions of limit for bounded operators are the following: the weak limit, w. limn=00 Ln —L, if Lnu converges weakly to Lu for every u EF; the strong limit, str. lim Ln = L, if Lnu converges strongly to Lu; the uniform limit, un. lim Ln = L, if ||L„ —L|| —>0, where || || for operators denotes their bound. It is clear that weak convergence follows from strong convergence and that strong convergence follows from the uniform one. It is known that w. lim Ln = L involves the boundedness of all ||Fn|| and the inequality ||Z,||^lim inf. ||F„||
Theorem II. If L = w. lim L„, then for the corresponding kernels we have A(x, y) =lim An(x, y) for every x, y in E. If L = un. lim Ln, then A„ converges uniformly to A in every set of couples (x, y) for which K(x, x) and K(y, y) are uniformly bounded.
The first part follows immediately, by the definition of weak convergence from
A(x, y) = (A(z, y), K(z, x))z = (L*K(z, y), K(z, *)).
= (K(z, y), LzK(z, y))z = lim (K(z, y), LnzK(z, x))z = lim An(x, y).
The second part follows easily from
| A(x, y) - An(x, y) | = | (K(z, y), (L - Ln)zK(z, x)) |
^\\K(z, y)\\z\\(L - Ln)zK(z, x)\\z
lZ\\K(z, y%z\\L - Ln\\\\K(z, x)\\2
= ||£ - Ln\\(K(x, x) K(y, y))1'2.
Consider now two orthonormal complete systems in F, {gm\ and {g„" } (in particular we may have gm= gm). The double system {gm(x)g„'(y)} is a complete orthonormal system in the direct product F®F. If A(x, y) belongs to the direct product we know that it is representable by an absolutely convergent double series
(10) A(x,y) = 23 <wg,l(x)g„("y)


 1950] THEORY OF REPRODUCING KERNELS 375
where the coefficients amn satisfy Z«." IgwI 2< °° and are given by
(11) amn = (¿'(y), (gl(x), A(x, y))x)y = (g'n'(y), Lg'm(y)).
Theorem III. For every bounded operator L, the series in (10) with coefficients given by (11) is convergent for every x and y in the sense
VQ _
(12) A(x, y) = lim Z Z ctmngm(x)g/'(y).
P,Q=ac m=l n=l
The A(x, y) belonging to the direct product F® F correspond to operators with finite norm.
Let Pp and P5". be the projections on the subspaces generated by gi i gi, • ♦ • • gi and g/' ,g{', • • ■, ga". It is clear that str. lim,,_w P¿ =1, str. limg=M F," =1. Consequently, for any u, v in F
(13) lim (P'q'v, LP'pu) = (v, Lu).
»,í=00
If we take now v = K(z, y) and u = K(z, x) as functions of z, we get P"v
=P'¿K(z,y)= Z&-"(»)2?ÖÖ.^> = Zíg¿(2)áW and (11)and (13)then
lead directly to (12). The norm of an operator L is given by 9Î(I/) = Zm-i||£gm||2 for any orthonormal complete system {gn}- It is independent of the choice of this system and may be finite or infinite. From (11) it is clear that
CO
Lg'm(y) = ^,a„ngn(y) n=l
by development in the system {g„" {.Consequently, ||Z<g4(y)l|2= Z"-i |°w|2 and yi(L) = Zm=i Z«=i I°w|2 which proves the second part of our theorem. 12. The reproducing kernel of a sum of two closed subspaces. Let F be a class with a r.k. K. We know that the r.k.'s of closed subspaces of F correspond to the projections on these subspaces. The problem of expressing the r.k. of the sum Fi@F2 oí two closed subspaces in terms of the r.k.'s Ki and K2 of these subspaces is therefore reduced to the problem of expressing the projection P on Fi©F2 in terms of the projections Pi and P2 on Fi and F2. In order to obtain this we shall at first prove the identity
[(P-Pi)(P-P2)]
(1) = P - Z PÁPtPl) ^ + P2(PlP2) ft"1 - (P2Pl) " - (P1F2) k] - (P2Pl) m.
4-1
We shall use the known properties of projections, namely: Pi = P1P = PPi = Pf, P2 = P2P = PP2 = Pl


 376 N. ARONSZAJN [May
Pi(P - Pi) = (P - Pi)Pi m 0, P2(P - P2) = (P ~ P2)P2 = 0.
Then, denoting the expression (P —Pi)(P —P2) by Q we have
QkPl m Qk-lÇp _ pi)(p _ pi)Pl = Qb-irp _ pi)(Pi _ APi)
= - <2'i-1P2Pi + Qk-lPiP2Pi.
If ¿>1, the first term is -<2*-2(P-P])(P-P2)P2Pi = 0, and we have
QkPí = Qk-ip1p2pu k > 1.
For i=lwe obtain
(?Pi = - P2F1 + P1P2P1.
Finally, we obtain by induction
(2) <2<Pi = - (P2Pi)* + Pi(P2Pi)k.
Further, we have
(3) Q = (P - Pi)(P - P2) = P - Pi- P2 + PXP2.
This gives Qn = Qn-i'p - P1 - P2 + pyp¿ = Qn-lp _ Q^IP, - Q^Pj + Q^PiP^
Since <2"-ip = Ç»-1, (3«-ip2 = 0, we get from (2)
Qn = q»-i _ Q»-ipj + (2»-ip1P2
= Q"-1 - [-(PiPi)""1 + P1(P2Pi)""1]
+ [-(P2Pi)"-iP2 + P1(P2Pi)"-1P2] = Q«-l + (P.PAn-l - P^P.^y-l _ p2(pip2)n-1 + (PlP2)n.
This expression is valid for w^2. Adding these equations side by side for n = m, m —i, • ■ ■, 2, and using the formula for Q given in (3), we obtain the required formula for Qm. This formula may be written in the form
P = [(P- Pi)(P - P2)]» + (P2Pi)TM (4) m
+ Z [FitP.p,)*-1 + p2(PiP2y^ - (p2Pi)* - (P1P2)*].
k=l
We shall prove now that for m—»», (P2Pi)m converges strongly to the projection P0 on the intersection F0 of Fi and F2. In order to do so we shall consider the operator L = P2Pi in the space F2. In this space L is a positive operator (and therefore symmetric) with bound not greater than 1. In fact, for uQF2
(P0P1U, P2Piu) = ||P2Pi«||z ^ |1Fiîî||2 = (Pi«, Pi«) = (Pi«, «) = (Pi«, Piu)
= (PgPi«, u) = ||Pi«||2 s ||«||2,


 1950] THEORY OF REPRODUCING KERNELS 377
(5) 0 ^ (Lu, Lu) ^ (Lu, u) ^ (u, u).
Consider now for any/G F the sequence [Lkf\. For£3:l, Lkf = P2PiLk~f EF2. Putting u = Lkf in (5), we get
0 è (Lk+y, Lk+f) ¿ (£*+»/,L»f) ^ (Lkf, Lkf),
0 ^ (L2k+if,Lf) á (L2kf,If) g (F2*-1/, Lf).
Consequently the sequence [Lnf, Lf)} is a decreasing sequence of positive numbers and therefore it is convergent. This gives
lim ||Fm/- I»/H2= bm [(Lmf,Lmf)- (Lmf,L"f)
m,n= oo
- (L'f, L"f) + (L'f, L'f)]
= lim [(L^~f,Lf) - 2(Z"+«-»/,Lf) + (F2-1/, F/) ] = 0
and thus Lmf converges strongly. This means that Lm converges strongly to some bounded operator P0. We have further Lm+1f=LLmf = LmLf, which, for m^> oo, gives
(6) LPof = Pof = PoLf.
Therefore LmP0f=P0f and Po/=lim LmP0f=Pof. In the subspace F2, F0 as a limit of symmetric operators is symmetric. Together with Fq/=Po/ it shows that in F2 the operator P0 is a projection. It is the projection on the subspace of all Pof. From (6) we get \\P2PiPBf\\^\\PiPof\\£\\Pof\\=\\P2PiPof\\. Consequently \\P2PiP0f\\ =||F1P0/|| =||Po/||, P2PiP0f = PiPof = Pof and Po/GFo = Fi• F2. Inversely if uEFi-F2, then Lu = P2Pxu = u and P0u = lim L"u = u. Thus, in F2, Po is the projection on F0. Then for any/GF, we have by (6) Pof = PoLf =P0P2Pif= projection of/on F0. In our formula (4), besides the series 23 and tne term (P2Pi)m we have still the expression (P —Pi)(P —P2)m. P —Pi is the projection on F'OFi, and POP2 is the projection onF'OF2, if we denote Fi©F2 by F'. Consequently for m^><», the last expression converges strongly to the projection on the intersection of (F'OFi) and (F'-OF2). But this intersection is reduced to the element zero because were there in it any element w^O, it would belong to F' and would be orthogonal to Fi as well as to F2. Thus, u would be orthogonal to Fi©F2 = F' which is impossible. In this way we finally obtain the desired formula for the projection P:
00
(7) p = Po + 23 [Pi^Pi)*-1 + p2(PiP2y-1 - (p2Pi)k - (PiP2)kl
k=l
The subspace Fi©F2 is defined as the closure of the subspace Fi+F2 composed of all sums/i+/2, fiEFu f2EF2. In general Fi + F2 is not a closed subspace.


 378 N. ARONSZAJN [May
Formula (7) is especially advantageous when Fi + F2 is closed and thus equal to F' = Fi0F2. Let us analyze this case more in detail. It will be convenient to make the non-essential assumption that
(8) F0 = FVF, = (0), that is, P0 = 0.
The angle between two elements (vectors) fy^O, f2y±0 is given by cos a = Re (A>A)/||/]||||A||- The minimal angle <j>,Oi£e/>^7r/2, between Fi and F2 is given by(10)
(9) cos <b= l.u.b. Re ,., !■'„*,■ for 0 ^ f G Fu 0 * /2 G F2.
IIAIIIIAII
It is easily seen that, for fiQFi, f2QF2,
(10) I(A.A)| ^llAllllACll0S<¿>, (11) IkiAllá HAcUos*, ||P2/i||^ HAcUos</>, (12) HA+ AH^ HAsUin*, HA+ AUè HAsUin*.
In (12), sin 0 is the greatest constant c=g0 for which an inequality of type II/i+AII^cIIaII is true. By a theorem of H. Kober [l] such inequality with c>0 is necessary and sufficient in order that Fi + F2 be closed. Consequently, we shall know that F' = Fi + F2 if we prove an inequality
(13) llA+ AllMiAii.
with any e;>0. Such a constant is necessarily less than or equal to 1 and it gives always an evaluation of the minimal angle <p:
(14) sin tj>^ c > 0.
The angle <f>being positive, the inequalities (11) show that the bounds of the operators (P2Pi)n in F2 or (PiP2)n in Fi are not greater than cos2n<£.Formula (7) may now be written in the form
P = (Pi - P1P2 + P1P2P1 - P1P2P1P2 + • • • )
+ (P2 - P2Pi + P2PiP2 - P2P1P2P1 + • • • )
and the two series are uniformly convergent to the operators Qi and Q2 which
give the decompositionof/GFi+F2 in f=Qif+Q2f, Çi/GF, QrfQF,.
It should be remarked that the decomposition of the series in (7) into the two series (15) is not possible when 0 = 0, as the operators Qi and Q2 are then unbounded. |£l When the series in (15) are used for computation it is very easy to get
(10) The notion of a minimal angle between two subspaces seems to have been first introduced by K. Friedrichs [l].


 1950] THEORY OF REPRODUCING KERNELS 379
estimates for the remainder. Usually we shall want to compute, for / and g in F, the value of (/, Pg) = (/, Qig)+(f, Q2g). It is clear that when we stop in the series of Qi at the wth term Pf* = (-\)n-lPiP2Pi ■ ■ ■, then the remainder Rf' of this series will be given by
(16) Ri = — Pi Q2 for odd n, Ri = — Pi Qi for even n.
We have similar developments for the second series defining Q2. Consequently, the error in (/, Qig) (for example when n is odd) is given by (/, Rig)
= -(Pin,7. Q*g)
en) K/,^)iáiipr/iiiM- *
By (12) we have ||(?2g|| ís(l/sin c/>)¡|g||. As PÍ"' is already computed, Pf* is known also and we can compute ||PÍB)*/||. This will give quite a precise evaluation of the error. Without knowing Pi we can evaluate HPi"'*/!!
á |l/l| cos-ty.
Even in case c/>= 0 we could still evaluate the error in (/, Pg) if Qig and Q2g exist and if we can evaluate their norms. Still another evaluation of error (preferable as an a priori evaluation), in the case ci>>0, is obtained directly from (4):
m
p - 23 [ ]=[(-?- Pi)(p - p*)\m + (PtPi)m
*-i
It can be proved that the minimal angle of F'OFi and F'-&F2 is the same as between Fi and F2. Consequently
|| [(P - Pi)(F - P0]"|| ^ cos2TM-14>, ||(P2PiH| Ú cos2—1cf.,
*-£[ *_i < 2 cos2""-1 <t>,
where || || signifies bounds of operators. In case of a sum of more than two subspaces F' = FiffiF2ffiF3ffi ■ • -we can still express the projection on F' in terms of projections on Fi, F2, • • • , but the formula will be much more complicated than in the case of two subspaces and for this reason may not be as valuable. Let us consider now the translation of our formulas in terms of the reproducing kernels Ki, K2, and K' of the classes Fi, F2, and F' = Fi©F2. We shall suppose that the classes Fi and F2 have no function ^0 in common, that is, Fi-F2=(0). To the projections Pi, P2, P there correspond (in the sense of §11) the kernels K\, K2 and K'. To each term in the series (7) or (15) there corresponds a kernel given by the following table of correspondence
P^K'(x,y), Pi^Ki(x,y), P2^K2(x,y),


 380 N. ARONSZAJN [May
PiP2^\i(x, y) = (Ki(z, y), K2(z, x))m
P2Pi<->Ai(y, x) = (K2(z, y), Kx(z, x))z,
(PiP2y^\n(x,y), (P2Pi)n<->An(y, x),
where
An(x, y) = (Ai(z, y), \n-i(x, z))z = (AKl(z, y), A„2(x, z))„ »i + n2 = n,
Pi(P2Pi)" «->Al (*, y) = A'„(y, x) = (Jdfe y), An(z,*))„
P2(PiP2)n^A"(x, y) = A'r! (y, x) = (K2(z, y), A„(«, z))z.
Formula (15) can now be written in the form
CO
K'(x, y) = Z (A„-i(x, y) + A„_i(x, y) — A„(x, y) — An(y, x))
(18)
= Z (A*-i(x, y) —An(x, y)) + Z (A„_i(x, y) — A„(y, x)).
n=l n=l
If we use these series to compute K'(x, y) for given points x and y, we shall represent it in the form
K'(x, y) = (K'(z, y), PzK'(z, x)) = (K(z, y), PzK(z, x))
and apply our evaluation of error to this form. 13. Final remarks in the general theory. In the present section we shall collect a number of shorter remarks about the nature of classes of functions with reproducing kernels and of their norms, and concerning some relations between the classes and their r.k.'s. (A) Classes of functions for which a r.k. exists. (R.K.)-classes. Consider a set E and a linear class F of functions defined (and finite) everywhere in E. The problem which arises is to find under what circumstances we can define a norm in F giving to F the structure of a Hubert space with a r.k. For abbreviation we shall call such classes of functions (R.K.)-classes.
Theorem I. In order that the class F (not necessarily linear) be contained in a (R.K.)-class it is necessary that there exist an increasing sequence of sets F1CF2C • ■• , E = Ei+E2+ ■■■, and for each fy*0 of F a positive number N(f), so that the functions f(x)/N(f) be uniformly bounded in each En.
In fact if Fi is the (R.K.)-class containing F, || ||i and Ki its norm and kernel, we define as £„ the set of all yGF with Ki(y, y)ikn and as N(f) the norm ||/||i. Then, for each yGFn and /GFCF we have |/(y)| = | (f(x), Ki(x, y))i| ^||/||||iî:,(x, y)\\i = N(f)((Ki(y, y))1'2 and \f(y)\/N(f)^n^2. The necessary condition of Theorem I is not always satisfied even for an enumerable sequence of functions. As an example, consider in the interval F=(0, 1) the sequence of functionsA(x) = 1/|x —rn| for xy^rn and fn(rn) =0.


 1950] THEORY OF REPRODUCING KERNELS 381
Here \rn\ is a sequence of numbers everywhere dense in E. By an easy topological argument we prove that the sequence of functions /„ does not satisfy the condition of Theorem I.
Theorem II. For an enumerable sequence \fn(x)} the condition of Theorem I is also sufficient in order that this sequence be contained in a (R.K.)-class.
In fact, consider an upper bound Mm<<*> for \fn(x)\/N(f), »=1, 2,- • • , xEEm. We write
Clearly, the series is absolutely convergent and represents a p. matrix. Each term of it
KÁx'y)=2»MiN2(fyÁx)m
is also a p. matrix and Kn<£K. Theorem I of §7 gives then for the corresponding classes F„CF. Obviously Fn is the one-dimensional class generated by/„. Therefore/„ G F and {/„}CF. The condition of Theorem I is certainly not sufficient in general. This may be shown by a simple set-theoretical argument. Let us consider namely the class F& of all bounded functions on E. We can then take En = E, N(f) = l.u.b. |/(x)|. If K is the power of F then the power of a (R.K.)-class F is fóNo(as the functions K(x, y)=hy(x) form a complete system in F). On the other hand, the power of the class Fb is =cN (c is the power of continuum) and for N> No, cK>N*o. (B) Convergence in classes with reproducing kernels. Consider a class F with a r.k. K. We know that if /„ converges strongly to / in F, then it converges uniformly in every subset of F where K(x, x) is uniformly bounded. Therefore the sequence {/„} satisfies the condition (1) fn(x)—*f(x) for every xEE, the convergence being uniform in every set of an increasing sequence of sets FiCF2C • • ■with F = Fi+F2+ ■• • . Consider now the class í> of all functions defined in F. In $ we can introduce a notion of limit as follows:
(2) f(x) = .$-lim fn(x), if condition (I) is satisfied.
It is clear that in general the sequence of sets En will depend on the sequence {/n}- We can now formulate the following theorem.
Theorem III. In every class F with a r.k., the strong convergence of fn(x) to f(x) involves i>-lim/„(x) =/(x).
It should be noted that the weak convergence in F does not involve in


 382 N. ARONSZAJN [May
general the ^-convergence. But there are important cases where even weak convergence involves «^-convergence. Such cases were considered in §2, (5). (C) Relations between (R.K.)-classes and corresponding norms and reproducing kernels. To a p. matrix there corresponds a uniquely determined class and norm, but to a (R.K)-class there correspond infinitely many norms giving to it the structure of a Hubert space with a r.k. Consequently to a (R.K.)-class there correspond also infinitely many p. matrices which are r.k.'s of the class for convenient norms. If the norm || || corresponds to a (R.K.)-class F, the norm || ||i = c|| ||, e>0, obviously also corresponds to F and the corresponding r.k.'s K and FJj satisfy 1
Ki(x, y) = — K(x, y).
c
In fact, the scalar product ( , )i is clearly =c2( ,) and thus f(y) = (f(x), K(x, y))=c2ifix), il/c2)Kix, y)) = (/(x), (l/c2)F(x, y))i. We shall now have to apply an important theorem of S. Banach [l ] in the theory of linear transformations. Let F be a linear transformation of a linear subspace F' of a complete space F on a linear subspace F{ of a complete space Fi. The subspaces F' and Fi'are not necessarily closed. The transformation T is called closed if
from {/„}CF',/n->/GF, and F/n->/,GFi follows/GF',/i G F/ and Tf=f.
Banach's Theorem. If T is a closed linear transformation of F' on F{, F'CF, F{ CFi, F and Fi complete normed vector spaces and if F' is a closed subspace of F, then T is continuous and consequently bounded ithat is, there exists a M>0 with \\Tf\\i^M\\f\\). The image F{ is either = Fi or of first category in Fi.
Before we apply this theorem we shall prove the following lemma:
Lemma. Let Fi and F2 be classes with r.k.'s and let F0 be their intersection Fi-F2. The correspondence transforming fEFo considered as belonging to Fi into f considered as belonging to F2 is a closed linear transformation.
In fact, suppose that {/„}CF0 and that/„ converges strongly to/' in F] and to/" in F2. Following Theorem III
fix) = *-lim/n(x) =f"ix). .
Therefore,/'=/" G Fo, which proves the lemma.
Theorem IV. Let Fand FiCF be iR.K.)-classes and || ||, || ||i some
norms corresponding to F and Fi. Then there exists a constant M>0 such that
WfUMWfWiforfEFt.
In fact the identical transformation of Fi considered as subspace of Fi


 1950] THEORY OF REPRODUCING KERNELS 383
on Fi as subspace of F is closed (following the lemma), Fi is a closed subspace of Fi, and thus our theorem follows immediately from Banach's theorem.
Corollary IVi. Let || || and || ||i be two norms corresponding to the same (R.K.)-class F. There exist two positive constants m and M such that w||/||
ú\\f\\iúM\\f\\,forfeF.
Theorem IV, together with Theorems I and II from §7 and with the remark that to norm M\\ || corresponds the kernel (l/M2)K, gives immediately the corollaries:
Corollary IV2. Let K and Ki be two p. matrices, Fand Ft the corresponding classes. In order that FiCF it is necessary and sufficient that there exists a positive constant M such that Ki^iMK.
Corollary IV3. Under the hypotheses of corollary IV2, in order that Fi = F it is necessary and sufficient that there exist two positive constants m and M such that mK<£Ki<KMK.
The second part of Banach's theorem together with our lemma leads to the following remark which belongs to the subject matter of section (A). Remark. If {Fn\ is a strictly increasing sequence of (R.K.)-classes, then their sum F= Z-^« is n°t a (R.K.)-class. In fact, were there a norm || in F giving it the structure of a Hubert space with r.k., the subspaces FnC.F would be of first category in F and therefore F would be of first category in itself which is impossible. (D) Connection with existence domains in a Hilbert space. We shall now use the notion introduced recently by J. Dixmier [l] of domains of existence in a Hilbert space. A linear subset of a Hilbert space is called a domain of existence, d.e., if there exists a closed linear transformation defined in this subspace and transforming it into a subspace of another Hilbert space (which, in particular, may be identical to the first Hilbert space). The d.e.'s D in a given Hilbert space § with norm | || may be characterized by the following property: there exists a norm || |i defined in D giving it the structure of a Hilbert space and satisfying
(3) ||â||i ^ ||ä|| for every h QD.
In fact, if D is a d.e., then we consider the linear closed transformation T of D into a subspace of some Hilbert space ¡q', with the norm || ||'. It is then clear that the norm || ||i defined by
IW-IîIHTI+M"
gives D the character of a complete Hilbert space which satisfies condition (3).


 384 N. ARONSZAJN [May
On the other hand, suppose that a norm || ||i is defined in D satisfying (3) and giving D the character of a complete Hilbert space. Then the correspondence transforming any element of D, considered as a subspace of §, into the same element considered in the Hilbert space D (with norm || ||i) is obviously a closed transformation and D is therefore a d.e. Using Theorem II from §7 and Theorem IV of section (C) we prove now immediately the following theorem.
Theorem V. If a class of functions F forms a Hilbert space with a reproducing kernel, then for any linear subclass FiCF, the necessary and sufficient condition in order that Fi be a (R.K.)-class is that Fi be a d.e. in F.
If we have two classes of functions Fi, F2, with reproducing kernels, we can combine these two classes in different ways in order to form new classes. Let us consider in particular the following classes of functions: Fo=Fi-F2 and F=Fi + F2.
Theorem VI. // Fi and F2 are (R.K.)-classes, then the same is true of the classes Fi-F2 and Fi + F2.
Proof. The linearity of the classes is obvious. We take firstly the intersection F0. With any norms || ||i and || ||2 corresponding to Fi and F2 we define the norm in F0 by the equation
ll/ll-2II/II+ÎMil
This norm clearly defines a quadratic metric in Fo satisfying all the required properties. For instance, the completeness of Fo results immediately from the lemma of section (C). As ll/lli=|l/l11for/GFo, Theorem II, §7 gives then the existence of a r.k. for F0. In the case of the sum, F= Fi+F2, we may apply the theorem of §6 which states that Ki and K2 being the r.k.'s with the norms || ||i and || ||2 of Fi and F2, Ki+K2 is the reproducing kernel of our class F. Besides the operations of • and +, we can also introduce the direct product Fi®F2 as defined in §8 as another operation leading to a (R.K.)-class when Fi and F2 are (R.K.)-classes. The class Fi®F2 however is defined not in E but in the product set EXE. If we take its restriction to the diagonal set of all pairs {x, x}, we get a class of functions defined in E. It can be proved that this class does not depend on the choice of norms in Fi and F2 as long as the norms give to Fi and F2 the structure of a Hilbert space with a r.k.
Part II. Examples
1. Introductory remarks. In this part we shall give examples showing how our general theory may be applied in particular cases and to what kind of results it leads. With a few exceptions we will not go into the details of calcula


 1950] THEORY OF REPRODUCING KERNELS 385
tion and will not give in explicit form the formulas and relations obtainable by our general methods. We shall treat essentially two kinds of kernels: the Bergman's kernels F(z, Zi) and the harmonic kernels H(z, Zi). (1) Bergmari s kernels. These kernels correspond to a domain D in the space of n complex variables z=(z(-r>, z(2), • • ■, z(n)). We consider the class 2í=2íz> of all analytic regular functions in D with a finite norm given by
11/112
\f(z'-l\zm, ■■■ ,z^)\2dx^dy^dx^dy^ ■■■dx^dy<-n\
where z(A)=x(4) -\-iyw. The class 21 possesses a reproducing kernel K = Kd—the Bergman's kernel corresponding to D. In our examples we shall consider essentially the case of plane domains D. li D is multiply-connected we shall consider also the reduced Bergman's kernel K'(z, Zi), which is the reproducing kernel of the subspace 21' of 21consisting of all functions of 21with a uniform integral j'fdz. If D is of finite connection n, the complementary subspace 2I-0-2I' is (» —l)-dimensional and is generated by n functions to„' (z) (between which there is the linear relation 23w* =0) defined in the following way: if Bk, k=\, 2, • • • , », are the boundary components of the boundary B of D, to* is the derivative (which is uniform) of the multiform analytic function to* whose real part is the harmonic measure w* of D corresponding to Bk, that is, the harmonic function regular in D, equal to 1 on F*, and vanishing on all the other components Bi. The functions w¿ belong always to 21 and are orthogonal to 21'. We have the relation
K(z, zi) = K'iz, zi) + 23 Cifwliz)w'iizi),
i,i
where 23 is the r.k. of 21021'. Consequently the matrix {ca} is definite positive (see §3) and it is the conjugate inverse of the Gramm 's matrix { (to/ , to/ )}. Bergman's kernels possess an important property of invariance: in case of domains in the space of » variables z(1), • • • , z(u>,if T represents D pseudoconformally on D', then
FV(z\ z{)dTiz)dTizi) = KDiz, zi).
Here, z'=Tiz), zi =F(zi), and c)F(z) is the Jacobi determinant of T. In the case of domains in the plane, if /(z) represents D conformally on D', this formula takes the form
KD>iz',z{)-t'iz)VÔÎ) = KDiz,Zi).
-,


 386 N. ARONSZAJN [May
The importance of the Bergman kernels lies in the possibility they offer of generalizing different theorems on analytic functions of one complex variable to functions of several complex variables (such as Schwarz's lemma, distortion theorems, representative domains in pseudo-conformal mappings). In the case of one variable almost all the important conformai mappings are expressible in terms of these kernels. For instance if D is a simply connected domain, the mapping function £"=/(z, z0) which represents Dona circle |f| <R in such away that the point ZoG-0 goes into f = 0and/'(z0, z0) = l is given by
/(*, zo) = —- f K{t, so)*.
K(zo, Zo) J,,
(2) Harmonic kernels. Consider in a plane domain D (we could consider also a domain in «-dimensional space) the class $8=93z>of all regular harmonic functions (in general complex-valued) with a finite norm given by
11*=1f1f* \h\2dxdy, z= x+ iy.
This class possesses a reproducing kernel which will be denoted by H(z, zi). It should be remarked that another harmonic kernel is often considered, namely the one which corresponds to the Dirichlet metric
11*=1f1f* [|*'*|+2 \h'y\2]dxdy.
This kernel is easily expressible by Bergman's kernel and consequently does not present any additional difficulties to the ones encountered in the study and computation of Bergman's kernels. The situation is different for the kernel H. Even for very simple domains (for instance for a rectangle) there is no known explicit expression of H even in the form of an infinite development. (We disregard here the developments in terms of a complete non-orthogonal system which are always possible to establish for a r.k., but whose coefficients are quotients of determinants of growing orders.) One reason for the greater difficulty of the investigation of the kernels H(z, Zi) as compared to Bergman's kernels lies in the fact that H has no such invariancy property vis-à-vis conformai transformations as have Bergman's kernels. The interest of the kernel H lies in its connection with the biharmonic problem which governs the question of equilibrium of elastic plates. The kernel H gives a simple expression for a function u(z) such that u = du/dn = 0 on the boundary B of D and AAw = <pin D, for a given function <j>.


 1950] THEORY OF REPRODUCING KERNELS 387
Supposing that we know a function \j/ such that A\f/= <j>(we can take as \¡/ the logarithmic potential of <f>i:^(z) = il/ir)ffr> log | z —z'\<piz')dx'dy') we get for u the expression (where g is the ordinary Green's function)
„(e)= - f f g(z,z')dx'd[y'Vf/)~ f f H(z',z")t(z")dx"dy"~].
The Green's function gn(z, Zi) of the biharmonic problem, satisfying AAg/j = 0 for Z7±Zi,gn = dgn/dn = 0 on the boundary, is given by
gn(z, zi) = I \ g(z, z')g(z'. zi)dx'dy'
- jj giz, z')dx'dy' jj Hiz', z")giz", zi)dx"dy".
These formulas were essentially noticed already by S. Zaremba [2]. 2. Comparison domains. Consider two domains in the plane, D and D', DC.D'. The kernels KD> or Hd>, restricted to the domain D, are reproducing kernels of classes 21° or Sß° formed by the restrictions of functions from 21d' or 33s'. As any analytic or harmonic function vanishing in D vanishes everywhere, any function f0 of 21°or SB0is a restriction of only one function/ from 21b-or 33d' and, following §5, Part I, the norm I/o |° = ||/||'- It is then clear that every /0G2I° belongs to 2IDand that ||/o||0è|[/o||. We can apply Theorem II of §7, I, which gives
00
(1) Kd- <3CKb, Kd' being the restriction of Kb- to D.
In the same way we get
0
(2) Hjy « HD.
If the kernel KD is known, we get immediately the well known estimates for the kernel KDi :
(3) FV(z, z) g KDiz, z), \KD>iz, zi) | á (Fj>(z, z)KD(zlt Zi)Y'2
for points z and zi belonging to D. But the relation (1) (or (2)) allows much better estimates. Suppose that the kernel Kr>>is known. For two points z and Zi in D take domains D" and A" such that zED"QD, ZiEDi CD and that the kernels KD" and KDi>be known (for instance circles). Then, from (1), we get Kniz, z)^KD'L'iz, z), Koizi, zi)^FJB;'(zi, zi),
| Koiz, Zi) — KD'iz, Zi) I2
(4) á [Kniz, z) - KD.iz, z)] [KDizi, zi) - ÄV(2l, zi)]
á [ÄV-(z, z) - KD'iz, z)][KD['izi, zi) -AV(zi, 2l)].


 388 N. ARONSZAJN [May
If we consider a boundary-point / where the boundary has a finite curvature and if we fix Zi and move z towards t, the estimate (3) will grow like 1/| z —1\. The estimate (4) by a convenient choice of the comparison domains D', D",andD{' will give a bound for | KD(z, Zi)\ growing only like 1/| z —t\ 1/2. To show the interest of this improvement, take D simply-connected and consider the conformai mapping of D on a circle |f| <P given by
1 r*
f = K(, *\ I K{Z' Z0)dZ
K{Zo, Zo) J 2„
Our problem will be to compute the point r on the circumference | f | =R corresponding to t on the boundary B. As the kernel K is not known we approximate it by a development in orthogonal functions. This development may converge fairly quickly inside the domain but in general it will not converge on the boundary and will converge less and less well the nearer we come to the boundary. To calculate r we have to integrate from z0 to the point t on the boundary. We cannot integrate term by term the development of K as it does not converge on the boundary. What we do then is to find, with the help of the estimate (4), a point Zi near t for which the integral f[\K(z, z0)\dz is sufficiently small. We can integrate the development of K term by term from Zo to Zi and obtain as good an approximation of t as we wish. It is clear that with the estimate (3) we would not be able to do this. 3. The difference of kernels. As we saw in §2, in DCZDX, the kernels K = Kd and K!=Kd¡ satisfy the relation Ki<£K (the kernel Ki being restricted to D). To illustrate the developments of §7, I, let us investigate the class of functions F2 corresponding to the p. matrix K2 given by
(1) K2(z, Zi) = K(z, Zi) — Ki(z, zi) z and Zi in D.
Following the notation in the proof of Theorem II, §7, I (where F = 3l, Fi = 3Ii), we introduce the operator L in SI by
(2) Lf = A(zi)= (/, Ki(z,zi))= ff f(z)Ki(z,zi)dxdy.
If we consider the Hilbert space $i of all functions u(z) in square integrable in Di with the norm
|«||i = I I | u(z) | dxdy,
the general property of r.k.'s as projections shows that/i(z), as function in D\, is the projection on 3Ii of the function/(z) =/(z) in D and =0 in Di —D. Consequently,
llAW^llllA(«)l|i^ll/W=|l|li/W||


 1950] THEORY OF REPRODUCING KERNELS 389
The second inequality may become equality for/(z)?^0 only in the case when Di —D is of two-dimensional measure 0 (for instance when D differs from Z>i only by some slits). We will exclude this case and consequently
(3) 11/iW=llUfW< ll/ll forf^O.
We introduce then the operator L' by
L'2 = I - L.
The subspace F0 is here reduced to 0 as 0yif=Lf is impossible in view of (3). Therefore F' = F=-2l and the only possibilities for the class F2 are: Io, F2= 2I or 2°, F2 is a dense subspace of 21. The first case represents itself always when D is completely interior to Di (DC.Di). In fact, the operator L is then completely continuous. To prove this we take a sequence {g(n)} C2Í converging weakly to gG2I. The functions |(n) converge then weakly in §i to g and their projections gin) on 21i converge weakly to gi. But the weak convergence in SIi involves uniform convergence of gi (z) towards gi(z) in any closed subset of Di, in particular in D (see section (5), §2, I). When we restrict the functions giB,(z) and gi(s) to D they become the transforms Lg(n) and Lg. Therefore, the uniform convergence of gin) to gi in D involves the strong convergence of Lg(n) to Lg in the space 21. Following our remarks after Theorem III, §7, I, the class F2 = F'= 21. To get the norm ||/||2 corresponding to the kernel K2, we have to find the solution g(z) of the equation
g-Lg = f
which exists and is unique for every /G2I. Then
ii/B-yr-iyî
where
gi(zi) = Lg = Il g(z)Ki(z,zi)dxdy.
Let us note that the operator L which in general has a bound not greater than 1 has here a bound less than 1. To illustrate the second case we have to take a domain having common boundary points with the boundary of D\. It seems probable that for every such domain D we shall be in the second case (at least if one of the boundary components of D arrives at the boundary of Di). To prove that we are in the second case, we have to show that the operator L has a bound = 1. Then L cannot be completely continuous (as the bound is not attained). The class Ft is a proper subclass of 21. The class F2 of all functions


 390 N. ARONSZAJN [May
h(¿) = g(z) - gi(z). where gi = Lg, g E SI,
is a proper subspace of F2, dense in F2. For such a function /2, the norm in F2 is given by
Il/II2 II II2 II II2
II/2II=2Ikll - l|gi||i
The class F2 in the metric of 21 is a dense subspace of 21. There are functions /G2Í which do not belong to F2 and for which, a fortiori, the equation f=g —Lg has no solution gG2I. (There may be such a solution, analytic in D but not in square integrable in D.) For two explicitly given domains DEDi, it may not be easy to prove that we are in the second case by using the property that the bound of F is 1. We can transform this property into another one, more easily proved. To this effect we shall consider for any function /iG21i the quotient
(4) Q(fi)= H/iUVll/iHi.
Lemma. In order that the bound of L be 1 it is necessary and sufficient that there exist functions f with Q(fi) as near 1 as we wish.
To prove this lemma we remark firstly that the l.u.b. Q(fi) for/iG21i is the same as the l.u.b. Q(Lf) for/G21. In fact the Lf form a dense subspace in the space 21i (otherwise there would be a giG21i, gi^O, with (gi, F/)i = 0 for every/G2I. Therefore (gi,/) = (gi, F/)i = 0 and gi = 0 in D which involves gi = 0 in DÏ). Consequently, there is for every /iG21i a function /G2Í with II/1-F/II1 as small as we wish. As ||/i-F/|| ^||/i-F/||i it is clear that Q(Lf) will approach Qifi) as nearly as we wish. Now, QiLf) can be represented as
(Lf,Lf) (F/, Lf)
(5) Q{Lf)= (Lf,Lf)i (Lf,f)
Our lemma amounts to the equivalence of the two properties, for any a, 0< a£l:
(6') (Lf,Lf) è a2(f,f) for allf G 21, (6") (Lf,Lf) ^ a(Lf,f) for allf E 21.
From (6") follows (6'):
(Lf,Lf) ^ a(Lf,f) =Sa(Lf,LfY'2(f,fY'2
(Lf,LfY'2^ a(f, fY'2, (Lf,Lf) ^ a2(f,/).
From (6') follows
(6'") (Lf,f)^a(f,f) for allf GZ.


 1950] THEORY OF REPRODUCING KERNELS 391
In fact, we have
(Lff) ^ (LfLfyufy2 rg a(ffy>2(f,fy2 = «(/,/).
From (6'") follows (6"): we use the fact that L is positive which gives (Lf, g)ú(Lf,fy'2(Lg, g)1'2.Then
(Lf, Lf) = (Lf,fyi2(LLf, Lf)"2 Ú (LffyiV2(Lf Lf)''2, (Lf,Lf)TM¿ aV\Lf, fy\ (Lf Lf) £ a(Lf /).
This proves our lemma. We shall apply the lemma to two domains DQDi having a common boundary point which belongs also to the boundary of the exterior of D. We suppose further that at this boundary point the boundaries of D and Dj have a common tangent. We can take the common boundary point as the origin O and the inner normal of the boundaries at this point as the positive axis. It is then easily verified that the functions
1
fn(z) =-j n — 1, 2, • • • ,
(nz + \y
for sufficiently great values of n, belong to 2L and that they satisfy the asymptotic equation
||/n|| ~||/»||i /orw->».
This shows that the l.u.b. Q(f) = 1 and that we are in the second case. Let us consider now another kind of example which we excluded till now. Namely, we shall suppose that the domain D differs from Dx only by a number of slits of finite length. It is then immediately seen that for a function AG2ti, considered as belonging to 21ÏC2I (21?= class 21i restricted to D), we have
11/=4I1IAlk
Consequently 21?is a closed linear subspace of 21 and the kernel K(z, Zi) —Ki(z, zi) corresponds to the subspace 2Ï02I?. 4. The square of a kernel introduced by Szegö. We shall now give an application of Theorem II, §8, I. Consider a domain in the plane with a sufficiently smooth boundary (for simplicity's sake we may suppose that the boundary curves are analytic). For this domain we shall consider a kernel, first introduced by Szegö [l], which we shall denote by k(z, Zi). This kernel corresponds to the class 5 of all analytic functions which possess in square integrable boundary values. As the functions are not necessarily continuous on the boundary we have to specify the meaning of the boundary values of the functions. We shall suppose that for such a function f(z), its integral F(z) is a continuous function in the closed domain (but F(z) may be a multi


 392 N. ARONSZAJN [May
form function). Then we suppose that for any two points tu t2 of the same boundary curve the difference F(t2) —F(h) may be represented by the integral
/, (2
f(t)dt,
¡i
where f(t) is defined almost everywhere on the boundary curves and is in square integrable there. The integral is taken over an arc of the boundary curve going from ti to t2. The function f(t) will be considered as the boundary value of f(z) in the boundary-point t. f(t) is completely determined by f(z) with exception of a boundary set of linear measure zero. The existence of boundary values of f(z) in our sense is equivalent to the absolute continuity of F(z) on the boundary. With the boundary values taken in this sense we define a norm in class S by the equation
ll/ll=223f l/«N*,
where C, are the boundary curves and ds is the element of length on the curve. For the functions of class 5 it is easily proved that the Cauchy theorem is still valid in the form
w - £ f JSLm.
J c„ t — z
From this it is immediately seen that the class possesses a reproducing kernel which is the kernel k(z, Zi) introduced by Szegö. Quite recently, in his thesis, P. Garabedian [l] proved that
(1) k2(z,zi) - — F(z, »0 + S ai,j»i iz)w¡ (zi)
4tt i,j
where K is the Bergman kernel for the domain and to/ are the functions introduced in §1. In cases of simply-connected domains Garabedian's formula takes a very simple form, namely:
1
k2iz, zi) = — F(z, zi).
4tt
In this case Theorem II, §8,1, gives a property of analytic functions which seems to have been unnoticed even for this simple case. Every function /(z) in square integrable in the domain D is representable in infinitely many ways by a series
(2) '00= 23**«**(*)


 1950] THEORY OF REPRODUCING KERNELS 393
where the functions <f>k(z)and \pk(z) are in square integrable on the boundary. In addition, we have the formula
(3) 4,rf f |fz) \2dxd=y min2323 f <l>k(t)*Áff)*dks(t)jÁf)ds,
J JD k I JC JC
the minimum being extended to all representations of f(z) in the form (2). In particular, we have the inequality
4tt f*Í* | <t>(z)\\K2zd)xdy¿ f | <¡>(\t2)dsf | t(t) \2ds.
J J D JC J C
In the case of a multiply-connected domain the problem is a little more complicated because of the presence of the functions w*. It can be proved then that if we replace the Bergman's kernel K by the reduced kernel K' (see §1) we have again a formula similar to (1) :
(4) k2(z,zi) - — K'(z,zi) + 23 ßi.M (z)W(zT)
4tt i,j
where, now, the ßi,j are the coefficients of a positive quadratic hermitian form, which means that 23».j represents a positive matrix. Consequently, the functions of the class corresponding to the kernel k2 are sums of functions in square integrable in D with a uniform integral (which form the class belonging to K') and of a linear combination of the to* (which form the class corresponding to 23¿.y)- The functions w* are in square integrable in D, and thus every function belonging to the class of k2 is in square integrable in D. Conversely, it can be proved that every function in square integrable over D belongs to the class of k2. By Theorem II, §8, I, we know that the functions belonging to k2 are of the form (2), but we will not be able to obtain a formula like (3) for the case of a simply-connected domain. However, a more complicated formula generalizing (3) does exist. In the present case of a multiplyconnected domain, we have still the property that the product <j>(z)\¡/(z)is in square integrable in D if </>and i¡/ are in square integrable on the boundary, but the inequality between the integrals will not be as simple as in the case of a simply-connected domain. 5. The kernel H(z, zi) for an ellipse. We shall construct the kernel H(z, Zi) for the ellipse D
99
(D D: _ + £-l, a>b,
a2 b2
by use of an orthonormal complete system (u).
(u) The system and the corresponding expression for the kernel were communicated to us by A. Erdélyi. It should be noted that the system was already introduced by S. Zaremba [l ] who also noticed that it is orthogonal and complete in the Dirichlet metric.


 394 N. ARONSZAJN [May
We write
(2) a = h cosh e, b — h sinh e,
(3) z = x + iy = h cosh f, f = £ + ir¡.
(3) gives us a conformai transformation of the rectangle R, 0<£<e, —7r<î7<ir on the ellipse (1) with the rectilinear slit —a<x<h. Consider in the rectangle R the analytic function pn(z) =sinh »f/sinh f (positive integer n). It is immediately seen that in the variable z the function is a polynomial of degree n —1. Consequently, all the polynomials in the variable z can be expressed as finite linear combinations of these polynomials for n = 1, 2, 3, • • • . Since the harmonic polynomials form a complete system in our class 93 of harmonic functions, the real and imaginary parts of pn(z) also form a complete system. On the other hand, it is easy to verify that these real and imaginary parts form an orthogonal system. This verification is made in an easy way by performing the integration in the rectangle R instead of the domain D. Using the formula
f f fix,y)dxd=y h2f f fix,y)| sinhf |W,
J J D J 0 J —T
one verifies easily that the sequence <£n(z)defined by
2 /«y2
<¿>2*-=2 —( — ) (sinh 2ne + n sinh 2e)-1/2 Re pn(z), n = 1, 2, • • • , h \ir/
(4) 2 /wY'2
«¿>2n-3= —( — I (sinh 2we — n sinh 2e)_1/2 Im pn(z), n = 2, 3, ■■■ ,
is orthonormal. We can then write the kernel of our class in the form
4 « ( Re p„(z) Re pn(zi) Im pn(z) Im pn(zx) \
(5) H(z, zi) =-¿-i n\-1-■-> .
h2ir „=i (sinh 2ne + n sinh 2e sinh 2ne — w sinh 2e;
6. Construction of H(z, Zi) for a strip. Our next example will use the theorem of the limit of kernels for decreasing sequences of classes (see Theorem I, §9, I). It will be at the same time an example of a representation of a kernel by use of a resolution of identity in a Hilbert space (see §10, I). Consider the kernel of §1 and suppose that in the ellipse
x2 y2
—+—= 1
a2 b2
the axis b<a remains fixed, while a—>». The ellipse in the limit will become the horizontal strip |y| <b. It is clear that our theorem on the limit of kernels applies in this case and we get the kernel H(z, Zi) for the strip as a limit of the kernels corresponding to ellipses. Before performing this passage


 1950] THEORY OF REPRODUCING KERNELS 395
to the limit, we shall at first make a few preliminary remarks. As in the preceding paragraph, we consider the quantities h and e given by o = A sinh e,a —h cosh e, b being fixed and a—»». We see immediately that h—*» and e—»0in such a way that Ae—>ô. In the conformai mapping, z = h cosh f we introduce a new variable f by the equation
■K
2
Then z = A sin **£', and the ellipse with the slit along the real axis going from +h to —a is transformed in the rectangle
3x IT
Rt, 0 < ? < 1,-< V < — •
2e 2e
Consider a point z in the horizontal strip |y| <b. For sufficiently large values of h the ellipse will contain z. Suppose that Im z>0, then the corresponding f will lie in the upper half of the rectangle Rt and for A—>», f—>z/6i. The point f " =f' —iri/e will then correspond to the conjugate point z, so that (f " +Tri/e)-J>zi/b. If we now return to the formula for the kernel from §5 and replace the function pn(z) by the expression sinh wf/sinh f, then replace f by tÇ'+iri/2 and separate the series which expresses the kernel H (see (5), §5) into parts corresponding to even and odd indices, we can write the kernel in the form of a sum of four series:
cos mef' cos ineÇ{
Im-Imco-s ¿ef cos t'efi
sinh 2we — n sinh 2e
sin intV sin in&i
Re-Rceo-s—tef cos «£i
sinh 2w€+ w sinh 2e
sin ¿wef' sin ineÇ{
Im--Icmo-s î'ef' cos í'ífi
sinh 2m€— « sinh 2e
For A—*», if we denote n/h by ¿ and if we then notice the asymptotic formulas Ae~è, nt~bt, n sin 2€~2&/, it is immediately seen that the series represent approximating Riemannian sums for the integrals
cos intç cos ¿wefi
Re-Re
4 n cos îef ' cos ¿«fi'
t* n odd h sinh 2»e + n sinh 2e
X« n odd «
+1*£ 7
IT ft n even **
+1*E 7
TTrl n even "


 396 N. ARONSZAJN [May
Re cos ibt? Re cos ib%{ 2 /"° Im cos ibl{' Im cos ibtÇl -dt,
2 n " Ke cos ibtÇ' Re cos ibtÇi 2 r °° ■
— \ t-dt-\-t
rc J o sinh 2bt + 2bt ir J 0
2 /■» Re sin ¿J/f' Re sin i¿>//f 2 /• '
+ —I /---— dt+ —I
ir J o sinh 2£>-¿f- 2e¿ ir J o
sinh 26/ - 2bt
2 r Re sin ibt? Re sin x'ô/f/ 2 /"" Im sin ibtÇ' Im sin ¿&/f/
/-dt,
1o sinh 2bt — 2bt
when we subdivide the infinite interval (0, + °° ) into equal intervals of length 2/h and in each interval take the value of the integrated function in the center (for the first two series) or in the right end (for the two last series). The convergence of these sums towards the integrals for A—»=° is easily verified and in this way we obtain for the kernel of the horizontal strip the expression given by the above four integrals where we replace f' and fí by the values z/bi and Zi/bi:
2 /"° Re cos zt Re cos Zit + Re sin zt Re sin zit
H(z, zi) = — I -tdt
it J o sinh 2bt + 2bt
2 /"° Im cos zt Im cos Zit + Im sin zt Im sin zit
H-j -tdt.
t J o sinh 2bt — 2bt
This integral representation of the kernel corresponds to a resolution of identity in the Hubert space S3 corresponding to the strip. This resolution of identity has a quadruple spectrum (see §10, I) defined by the following four functions/*(z, X):/*(z, X) =0 for XgO, for X>0
sin zX 1 — cos zX
/'A sin zX
Re cos ztdt = Re-> /2(z, X) = Re 0z z
sin zX 1 — cos zX /3(z, X) = Im-' /4(z, X) = Im
It is easily verified that these functions satisfy the conditions (a) and (b) from §10, I. The condition (c') results from the fact that the functions /* determine the r.k. Hiz, zx) of the class So by the formula above. 7. Limits of increasing sequences of kernels. In the preceding section we had an example of a limit of decreasing sequence of classes and kernels. We shall give here an example of an increasing sequence of kernels. Consider the Bergman's kernels Kn for a decreasing sequence of simplyconnected domains Dn such that D„+iQDn and F = lim Dn = Di-D2- ■ • ■consists of the two closed circles C\ : | z —21 ^ 1, and C2: | z + 21 ^ 1, with the segment of the real axis F —lgx^l,y = 0. Following the general theory of §9, I, we have to consider the set F0 where F0(z, z) = lim F„(z, z) < oo. Every point of the open circle Ci belongs to F0. In fact, if Ka) is the Bergman's kernel for Ci, by the method of comparison domains (see §2) we get


 1950] THEORY OF REPRODUCING KERNELS 397
Kn<KKiD in Ci and consequently K(z, z) =lim Kn(z, z) ^Ka)(z, z) for z in G* The same is true for zGG- We are going to prove that
(1) Fo = Ci + C2.
We have to show that for z0Q.E —E0, lim Kn(zo, z0) = ». We use again a domain of comparison. We take a closed line L defining an exterior domain 5 containing E and such that by a convenient translation we can approach L as near as we wish to z0 without touching E. The domain 5 will contain all Dn from some n onwards. For these n, Kny>Ks, therefore lim Kn(zo, zo) ^Ks(zo, Zo). The translation of the line L (and the domain S) will have on Ks(zo, zo) the effect as if the domain 5 were fixed and the point zo were moving towards the boundary L. As for Bergman's kernels of domains of finite connection we have the theorem that K(z, z) goes uniformly to + » when z approaches the boundary (12), we arrive at the result, lim Kn(z0, z0) = + ». For ZoGFv —Fo, with exception of z0= +1, we can take as L a sufficiently small circumference. For z0= +1, a circumference cannot do. We take then for L the boundary of a square, for instance, for z0 = + 1, we take the square: -€<x<l-e,e<y<l+e. Using the notation of §9, I, (B), we see immediately that the class F0 with the norm || o is here a subspace of the class F of all functions/(z) defined in the two open circles G and C2, analytic and regular in each (but/(z) in G is not necessarily an analytic continuation of f(z) in C2), with a finite norm
ll/ll=2 f f IA«)Vdxd+yf IA«)Vdxdy.
J J Ci J c¡¡
Consequently, the condition 2° of §4, I is satisfied and we obtain a functional completion F* of F0. Then, it is easily proved, by using general approximation theorems of analytic functions, that the space F* coincides with F
The r.k. of F is immediately seen to be given by:
K(z, zi) = 0 if z and Zi belong to different circles,
K(z, zi) = K(i)(z, Zi) if z and zi belong to G.
Similar results can be obtained if the domains Dn, n„+iC5» have an arbitrary intersection E = Di-D2- ■ • • . The set Fo is then the set of all interior points of E. 8. Construction of reproducing kernels by the projection-formula of §12,
(I2) This theorem is proved by using conformai mapping and the invariancy property of Bergman's kernels. For the kernels H for which the invariancy property is not true, a similar theorem has been proved only for domains with sufficiently smooth boundaries.


 398 N. ARONSZAJN [May
I. The formula of §12, giving the r.k. of a sum of two closed subspaces, may serve in many cases for the construction of kernels. We shall indicate here a few cases when it can be applied. (1) The expression for Hiz, zx) in terms of F(z, Zi). Consider for a domain D in the plane the classes 21and Sß. In spite of the similarity of the metrics in the two classes, the relationship between their kernels K and H does not seem a simple one. We shall get such a relation by using the formula (18), §12, I. To this effect we remark firstly that the class 58 is a class of complex valued functions, that is, every function A of the class is representable in the form h = hi-\-ih2, hi and A2harmonic and real-valued. Consequently, the class 21is a linear closed subspace of the class 93. Also the class 21of all antianalytic functions (that is, conjugate/(z) of analytic functions/) with a similar norm is a closed linear subspace of §. On the other hand, it is clear that every function he$? is representable as a sum
hiz) = /¿(i) + Mz)
with two analytic functions f and /2. These functions are uniquely determined with the exception of additive constants. In general, in this decomposition, the functions/i and/2 may be of infinite norm, that is, they may not belong to our classes 21 and 21. But when the boundary of D is not too irregular it may be proved that a dense subclass of SBis decomposable in this form with /i and/2 belonging to 21and 21which means that 33= 21©21. In order to avoid the indétermination of the above decomposition of AGS3 into/i+/2 because of the additive constant, we shall admit to the class 21only functions / satisfying the condition
J f fdxdy= 0.
With 21so fixed, the condition 21-21= (0) is satisfied. Consequently, we can apply our formula to calculate the kernel H. We obtain for H a development of the form
00
(1) Hiz, Zi) = 23 (A'n-iiz, si) + A^_i(z, 2i) — A„(z, Zi) — An(zi, z))
n=l
where the A's are expressible in terms of the r.k.'s of 21 and 21 following the formulas from §12. Since the kernel for 21 is F(z, Zi), the kernel for 21 is immediately seen to be FJ(z, zi)+const. The constant is easy to determine and we get for the kernel K of 21 the expression F(z, Zi) = K{zi, z) —l/cr where cr is the area of D. All the terms of the development of H are then expressible by repeated integration in terms of the kernel K alone. This development can serve to compute H when K is known. It will be especially useful when the domain is such that the subspaces 21 and 21 of 53


 1950] THEORY OF REPRODUCING KERNELS 399
form a positive minimal angle. This is equivalent to the fact that there exists a constant m>0 such that
«ll/llè ||/+ÄII foranyfQ21f, G¥.
It is easy to see that the last condition is equivalent to the following property of harmonic, real-valued functions AG33:
||Â|| ^ c||ä||, for some constant c > 0,
where A is the conjugate harmonic function of h (that is, h+ih is analytic). This property can be proved for domains with a fairly smooth boundary (continuous tangent), with at most a finite number of angular points with positive angles (see K. Friedrichs, [l]). Consequently we can apply (1) to compute the kernel H for a rectangle, which computation would be especially useful in view of applications to rectangular elastic plates. (2) We shall describe now a manner of applying our formula to calculate the kernels K. Let C be a closed set in the plane (not necessarily bounded) of twodimensional measure 0. Usually C will be composed of a finite number of arcs or closed curves. C decomposes the plane in a certain number of domains Di, D2, ■ • ■which together form an open set D. In D we consider the class of functions 21d formed by all functions which in each of the domains Dn are analytic and regular. We call such functions locally analytic and the set C their singular set(13). We shall suppose further that the functions of 21d have a finite norm given
by
(2) ||/||2= J*Jj/(z)|2ei*eiy.
The class 21d possesses a r.k. KD which is simply expressible by the Bergman's kernels Kon in the following way:
Kd(z, Zi) = KDn(z, Zi) if z and Zi belong to Dn,
Kd(z, Zi) — 0 if z and zx belong to two different D„'s.
There is no loss in generality if we suppose that C is bounded (we can use conformai mappings to reduce every case to this one). We shall denote by D0 the domain D„ containing ». Consider a decomposition of C in two closed sets
(4) C = C"> + G2>.
To every C(i) corresponds the complementary open set Dli> and we have
(5) D-DTM,D«K
(I3) The author introduced and investigated this kind of function in his thesis in Paris [2 ].


 400 N. ARONSZAJN [May
Every function /(s) locally analytic in D is decomposable into two functions /(z) =/i(z) +/2(z) each of which is locally analytic in the corresponding domain D(i) (see N. Aronszajn [2]). Two such decompositions differ by a function with the singular set C(1)• C(2). The classes 2Irjw)are clearly linear closed subspaces of 2Iz>(when we restrict their functions to the set D). The intersection of 2Idu) and 2Id(2)is equal to the class 21z>«where D* is the complementary set of C* = Cw ■C<2). The class 21d* is reduced to 0 when the intersection C* is a finite or an enumerable set. The equality
(6) 21D= Sfoi«e 2b<«
is not always true. For simplicity's sake we suppose now that C is not equal to 0 and is composed of a finite number of rectifiable arcs or closed curves, not reduced to isolated points, and that the same is true of C(1) and C(2). It can then be proved that the necessary and sufficient condition in order that (6) be true is that C*= C^ ■C'VO. Further, if C* = 0, then 2IbO[21du) ©2Ib(2)] is a one-dimensional space generated by the function to'(z) defined as follows: let A(z) ^Aecu.cw be the locally harmonic function in D, taking the value 1 on C(1) and 0 on C(2). Denote then by to(z) the function locally analytic in D (but not necessarily single-valued in the multiply-connected components Dn of D), whose real part is A(z). The derivative to'(z) =h'x —ih'v is single-valued in D and belongs to 2ti). A(z) is called the harmonic measure in D corresponding to C(1). From what we said, it results that we shall be able to calculate the kernel Kb by the formulas of §12 in the following cases: (1) When C*5¿0 and 2Íb«?í0 we can apply the general formula (7), §12, I, translating operators into kernels, in particular P, Po, Pi, and P2 into Kd, KD', Kom, and KDm. To calculate KD we have then to know KD-, K^m, and Ffl(2). (2) When CVO and 21j>-=(0) we can apply formula (18) §12, I. This case contains interesting particular cases; for instance in the case of a simply-connected domain bounded by a polygonal line C. We can decompose Cinto one side C(1) and a polygonal line C(2) having one side less than C. This gives an inductive process to calculate the kernel KD of the open set complementary to C. By this process we obtain, at the same time, the two Bergman's kernels for the interior and exterior of C. This is especially interesting as these kernels will give the conformai mapping functions of the domain on a circle. Another case in point is one when to a slit C(1) in the plane we add a rectilinear segment C<2), having only one point in common with C(1). This


 1950] THEORY OF REPRODUCING KERNELS 401
case may be of interest for the variational methods, as they were used by Loewner [l], for instance, in the problem of coefficients of schlicht functions. (3) When C*= 0, then 2Iz).= 0. We can apply formula (18), §12, I, to compute the kernel of 2Iz>(»©3Iz>(2i)f KDm and KD<.î>are known. Then, if we know the function w'(z), we add the function (l/||w'||2)w'(z)w'(zx) to the obtained kernel and arrive at the kernel Kd. The classes 2Ibo> and 2Ído> have, in this case, a positive minimal angle for which a lower estimate can be obtained (using the constant m from the inequality «||/i|| =||A+A|| as in §12, I) by the use of methods developed by the author in [3]. If we consider the reduced classes 2íí) of functions of 2Id with singlevalued integrals in every component domain Dn of D, we shall obtain a r. k. K'D expressible by a formula similar to (3) in terms of the reduced Bergman's kernels K'Dn. For the reduced classes we have always 2lí)= 21í>a>©2Ií>aa>nd in the case C* = 0, we shall calculate K'D directly by formula (18).
Bibliography #
N. Aronszajn 1. Sur les invariants des transformations dans le domaine de n variables complexes, C. R. Acad. Sei. Paris vol. 197 (1933) p. 1579,and vol. 198 (1934) p. 143. 2. Sur les décompositions des fonctions analytiques uniformes et sur leurs applications, Acta Math. vol. 65 (1935) p. 1. (Thesis, Paris.) 3. Approximation des fonctions harmoniques et quelques problèmes de transformation conforme, Bull. Soc. Math. France vol. 67 (1939). 4. La théorie générale des noyaux reproduisants et ses applications, Première Partie, Proc. Cambridge Philos. Soc. vol. 39 (1944) p. 133. 5. Les noyaux pseudo-reproduisants. Noyaux pseudo-reproduisants et completion des classes hilbertiennes. Completion fonctionnelle de certaines classes hilbertiennes.—Propriétés de certaines classes hilbertiennes complétées, C. R. Acad. Sei. Paris vol. 226 (1948) p. 456,
p. 537, p. 617, p. 700. 6. Reproducing and pseudo-reproducing kernels and their application to the partial differential equations of physics, Studies in partial differential equations of physics, Harvard University, Graduate School of Engineering, Cambridge, Massachusetts, 1948. S. Banach 1. Theorie des opérations linéaires, Monografje Maternatyczne, Warsaw, 1932. S. Bergman 1. Ueber die Entwicklung der harmonischen Funktionen der Ebene und des Raumes nach Orthogonalfunktionen,Math. Ann. vol. 86 (1922) pp. 238-271. (Thesis, Berlin, 1921.) 2. Ueber die Bestimmung der Verzweigungspunkle eines hyperelliptischen Integrals aus seinen Periodizitätsmoduln mit Anwendungen auf die Theorie des Transformators, Math. Zeit. vol. 19 (1923) pp. 8-25. 3. Ueber die Bestimmung der elastischen Spannungen und Verschiebungen in einem konvexen Körper, Math. Ann. vol. 98 (1927) pp. 248-263. 4. Ueber unendliche Hermitesche Formen, die zu einem Bereich gehören, nebst Anwendungen auf Fragen der Abbildung durch Funktionen von zwei komplexen Veränderlichen, Berichte Berliner Mathematische Gesellschaft vol. 26 (1927) pp. 178-184, and Math. Zeit. vol. 29 (1929) pp. 640-677. 5. Ueber die Existenz von Repräsentantenbereichen, Math. Ann. vol. 102 (1929) pp. 430446.


 402 N. ARONSZAJN [May
6. Ueber den Wertevorrat einer Funktion von zwei komplexen Veränderlichen, Math. Zeit, vol. 36 (1932) pp. 171-183. 7. Ueber die Kernfunktion eines Bereiches und ihr Verhalten am Rande, J. Reine Angew. Math. vol. 169 (1933) pp. 1-42, and vol. 172 (1934) pp. 89-128. 8. Sur quelques propriétés des transformations par un couple des fonctions de deux variables complexes, Atti délia Accademia Nazionale dei Lincei, Rendiconti (6) vol. 19 (1934)
pp. 474-478. 9. Zur Theorie von pseudokonformen Abbildungen, Rec. Math. (Mat. Sbornik) N.S. vol. 1
(1936) pp. 79-96. 10. Zur Theorie der Funktionen, die eine lineare partielle Differentialgleichung befriedigen, Rec. Math. (Mat. Sbornik) N.S. vol. 2 (1937) pp. 1169-1198. 11. Partial differential equations, advanced topics, Brown University, Providence, 1941. 12. A remark on the mapping of multiply-connected domains, Amer. J. Math. vol. 68 (1946)
pp. 20-28. 13. Funktions satisfying certain partial differential equations of elliptic type and their representation, Duke Math. J. vol. 14 (1947)pp. 349-366. 14. Sur les fonctions orthogonales de plusieurs variables complexes avec les applications à la théorie des fonctions analytiques, Mémorial des Sciences Mathématiques, vol. 106, Paris, 1947. S. Bergman and M. Schiffer 1. A representation of Green's and Neumann's functions in the theory of partial differential equations of second order, Duke Math. J. vol. 14 (1947) pp. 609-638. 2. On Green's and Neumann's functions in the theory of partial differential equations, Bull. Amer. Math. Soc. vol. 53 (1947) pp. 1141-1151. 3. Kernel functions in the theory of partial differential equations of elliptic type, Duke Math. J. vol. 15 (1948)pp. 535-566. S. BOCHNER 1. Ueber orthogonale Systeme analytischer Funktionen, Math. Zeit. vol. 14 (1922) pp. 180207. 2. Vorlesungen ueber Fouriersche Integrale, Leipzig, 1932. 3. Hubert distances and positive definite functions, Ann. of Math. vol. 42 (1941) pp. 647656. J. DlXMIER 1. Sur une classe nouvelle de variétés linéaires et d'opérateurs linéaires de l'espace d'Hubert. Propriétés géométriques des domaines d'existence des opérateurs linéaires fermés de l'espace de Hubert. Definition des opérateurs linéaires de l'espace d'Hubert par leurs domaines d'existence et des valeurs, C. R. Acad. Sei. Paris vol. 223 (1946) p. 971, and vol. 224 (1947) p. 180, p. 225. K. Friedrichs 1. On certain inequalities and characteristic value problems for analytic functions and for functions of two variables, Trans. Amer. Math. Soc. vol. 41 (1937) pp. 321-364. B. Fuchs 1. Ueber einige Eigenschaften der pseudokonformen Abbildungen, Rec. Math. (Mat. Sbornik) N.S. vol. 1 (1936) pp. 569-574. 2. Ueber geodätische Mannigfaltigkeiten einer bei pseudokonformen Abbildungen invarianten Riemannschen Geometrie, Rec. Math. (Mat. Sbornik) N.S. vol. 2 (1937) pp. 567-594. P. Garabedian 1. Schwarz' lemma and the Szegö kernel function, Trans. Amer. Math. Soc. vol. 67 (1949) pp. 1-35. P. Garabedian and M. Schiffer 1. Identities in the theory of conformai mapping, Trans. Amer. Math. Soc. vol. 65 (1948) pp. 187-238.


 1950] THEORY OF REPRODUCING KERNELS 403
I. Gelfand and D. Raikoff 1. Irreducible unitary representation of arbitrary locally bicompact groups, Rec. Math. (Mat. Sbornik) vol. 13 (1943) p. 316. R. Godement 1. Sur les fonctions de type positif. Sur les propriétés ergodiques des fonctions de type positif. Sur les partitions finies des fonctions de type positif. Sur certains opérateurs définis dans l'espace d'une fonction de type positif. Sur quelques propriétés des fonctions de type positif définies sur un groupe quelconque, C. R. Acad. Sei. Paris vol. 221 (1945) p. 69, p. 134, and vol. 222 (1946) p. 36, p. 213, p. 529. 2. Les fonctions de type positif et la théorie des groupes, Trans. Amer. Math. Soc. vol. 63 (1948) pp. 1-84. (Thèse, Paris.)
J. KOBER 1. A theorem on Banach spaces, Compositio Math. vol. 7 (1939) pp. 135-140. C. LOEWNER 1. Untersuchungen über schlichte konforme Abbildungen des Einheitskreises I, Math. Ann. vol. 89 (1923) pp. 103-121. J. Mercer 1. Functions of positive and negative type and their connection with the theory of integral equations, Philos. Trans. Roy. Soc. London Ser. A vol. 209 (1909) pp. 415^46. 2. Sturm-Louville series of normal functions in the theory of integral equations, Philos. Trans. Roy. Soc. London Ser. A vol. 211 (1911) pp. 111-198. E. H. Moore 1. On properly positive Hermitian matrices, Bull. Amer. Math. Soc. vol. 23 (1916) p. 59. 2. General analysis, Memoirs of the American Philosophical Society, Part I, 1935, Part II, 1939. Z. Nehari 1. The kernel function and canonical conformai maps, Duke Math. J. (1949). 2. On analytic functions possessing a positive real part, Duke Math. J. (1949). J. v. Neumann and F. J. Murray 1. On rings of operators, Ann. of Math. vol. 37 (1936) pp. 116-229. J. v. Neumann and I. J. Schoenberg 1. Fourier integrals and metric geometry, Trans. Amer. Math. Soc. vol. 50 (1941) pp. 226-251. M. Schiffer 1. The kernel function of an orthonormal system, Duke Math. J. vol. 13 (1945) pp. 529-540. 2. An application of orthonormal functions in the theory of conformai mappings, Amer. J. Math. vol. 70 (1948) pp. 147-156. I. J. Schönberg 1. Metric spaces and positive definite functions, Trans. Amer. Math. Soc. vol. 44 (1938)
pp. 522-536. 2. Positive definite functions on spheres, Duke Math. J. vol. 9 (1942) pp. 96-108. M. H. Stone 1. Linear transformations in Hilbert space, Amer. Math. Soc. Colloquium Publications, vol. 15. G. Szegö 1. Ueber orthogonale Polynome, die zu einer gegebenen Kurve der komplexen Ebene gehoeren, Math. Zeit. vol. 9 (1921) pp. 218-270. A. Weil 1. L'intégration dans les groupes topologiques et ses applications, Actualités Scientifiques et Industrielles, vol. 869, Paris, 1940. H. Welke 1. Ueber die analytischen Abbildungen von Kreiskörpern und Hartogsschen Bereichen, Math. Ann. vol. 103 (1930) pp. 437^49. (Thesis, Münster, 1930.)


 404 N. ARONSZAJN
K. Zarankiewicz 1. Ueber ein numerisches Verfahren zur konformen Abbildung zweifach zusammenhängender Gebiete, Zeitschrift für angewandte Mathematik und Mechanik vol. 14 (1934) pp. 97-104. S. Zaremba 1. L'équation biharmonique et une classe remarquable de fonctions fondamentales harmoniques, Bulletin International de l'Académie des Sciences de Cracovie (1907) pp. 147-196. 2. Sur le calcul numérique des fonctions demandées dans le problème de Dirichlet et le problème hydrodynamique, Bulletin International de l'Académie des Sciences de Cracovie (1908) pp. 125-195.
Oklahoma Agricultural and Mechanical College, Still water, Okla.