# Session Types Verification
# Unam 2021
## Ciro Iván García López

### Abstract

This project searches to verify the Subject Reduction and liveness Theorems using Coq. The work uses
the typing system proposed in Heuvel, B. & Perez, J., Session Type Systems based on Linear Logic: Classical versus Intuitionistic. 

### Introdución

Heuvel & Perez [1] proposed the <img src="https://render.githubusercontent.com/render/math?math=\pi">-ULL type system. This system search for a Curry-Howard relation between the classic linear logic and the <img src="https://render.githubusercontent.com/render/math?math=\pi">-Calculus. Actually Charguéraud [2] speaks about the importance of implementing this kind of theories due to the concepts that are involved.

Nevertheless the verification of this kind of systems is not easy. The representation for free and bound variables are critical due to the notion of <img src="https://render.githubusercontent.com/render/math?math=\alpha">-equivalence. De Bruijn proposed a representation known as Bruijn indices; such representation requires the definition of the shift functions [3]. This functions are critical in the representation and should be implemented without bugs .


In [3] Charguéraud intoduces the locally nameless representation; in this representation the bound variables are represented in the same way as Bruijn Indices and the free names remains represented as strings. Within this framework the notion of <img src="https://render.githubusercontent.com/render/math?math=\alpha">-equivalence is no longer require, and understanding the representation is easier than the Bruijn Indices. 

One of the mayor drawbacks in the LN representation is that there exists terms that does not have any sense. Hence is require the locally closed predicate in order to refer to the well formed expresions.


### Referencias: 
1. Bas van den Heuvel and Jorge A. P ́erez.  Session type systems based on linear logic: Classicalversus intuitionistic.Electronic Proceedings in Theoretical Computer Science, 314:1–11, Apr2020.
2. Arthur Chargu ́eraud.  The locally nameless representation.Journal of Automated Reasoning -JAR, 49:1–46, 10 2012.
3. David Castro, Francisco Ferreira, and Nobuko Yoshida.  Emtst: Engineering the meta-theoryof  session  types.   In  Armin  Biere  and  David  Parker,  editors,Tools and Algorithms for theConstruction and Analysis of Systems, pages 278–285. Springer International Publishing, 2020.
4. Kohei Honda (1993): Types for Dyadic Interaction. In Eike Best, editor: CONCUR’93, Springer Berlin Heidelberg, Berlin, Heidelberg, pp. 509–523, doi:10.1007/3-540-57208-2_35.
5. Luís Caires, Frank Pfenning & Bernardo Toninho (2012): Towards Concurrent Type Theory. In: Proceedings of the 8th ACM SIGPLAN Workshop on Types in Language Design and Implementation, ACM, pp. 1–12, doi:10.1145/2103786.2103788.
6. Davide Sangiorgi & David Walker (2003): The Pi-Calculus: A Theory of Mobile Processes. Cambridge University Press.
7. Jean-Yves Girard (1993): On the Unity of Logic. Annals of Pure and Applied Logic 59(3), pp. 201–217, doi:10.1016/0168-0072(93)90093-S.
