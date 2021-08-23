# Tarea 2 - Verificación Formal 
# Unam 2020-II
## Ciro Iván García López - Cta: 520463240

### Objetivo

Mecanizar en Coq el artículo: Heuvel, B. & Perez, J., Session Type Systems based on Linear Logic: Classical versus Intuitionistic. 

### Introdución

En [1] se presenta el sistema de tipos <img src="https://render.githubusercontent.com/render/math?math=\pi">-ULL, dicho sistema busca establecer una relación Curry-Howard entre un pedazo de la lógica lineal y el cálculo <img src="https://render.githubusercontent.com/render/math?math=\pi">. A su vez, tal como se expone en [2] resulta importante la mecanización en sistemas de verificación formal de dichas pruebas dados los diversos factores que que emergen al desarrollar estos conceptos. 

No obstante la mecanización de estas teorías involucra manejar abstracciones, variables ligadas y <img src="https://render.githubusercontent.com/render/math?math=\alpha">-equivalencias, tarea que no resulta sencillo de abordar. Una primera aproximación a esta tarea son los conocidos índices de De Bruijn, concepto en el cual todas las variables obtienen un indice y se van modificando por medio de operaciones de corrimiento [3]. El manejo de índices de De Bruijn resulta complicado ya que su corazón, funciones de corrimiento, complejiza el razonamiento con los términos.

En [3] se introduce la "representación local libre de nombres" una segunda aproximación en la mecanización de variables, en esta representación se hace distinción entre variable libre y ligada lo cual permite eliminar la noción de <img src="https://render.githubusercontent.com/render/math?math=\alpha">-equivalencia y su manejo resulta más sencillo al de los índices de De Bruijn. El precio a pagar por la simplicidad de la representación local libre de nombres es el incremento en las reglas de la gramática y las proposiciones auxiliares, ya que se introducen términos no deseados en la gramática. 

Con el fin de poder hablar de los "Process" tal como estan definidos en [1] se introduce la operación "Process"

Otro de los requisitos que se deben cubrir durante la mecanización es que toda operación definida para sobre los "Process" es necesario verificar que esta bien definida, es decir que operar sobre "Process" da como resultado un "Process"; por ejemplo considere el hacer reducciones sobre un término.

El repositorio contiene actualmente dos archivos:

- Documento.pdf : informe escrito en donde se detalla la mecanización. 
- Defs\_Proposition : Definiciones relativas a la noción de proposición.
- Props\_Proposition : Pruebas de algunos hechos que involucran los proposición.
- Defs\_Process : Definiciones relativas a la noción de proceso.
- Props\_Process : Pruebas de algunos hechos que involucran los procesos.
- Defs\_Typing : Definiciones relativas al sistema de tipos.
- Props\_Typing : Pruebas de algunos hechos que involucran el sistema de tipos.

### Referencias: 
1. Bas van den Heuvel and Jorge A. P ́erez.  Session type systems based on linear logic: Classicalversus intuitionistic.Electronic Proceedings in Theoretical Computer Science, 314:1–11, Apr2020.
2. Arthur Chargu ́eraud.  The locally nameless representation.Journal of Automated Reasoning -JAR, 49:1–46, 10 2012.
3. David Castro, Francisco Ferreira, and Nobuko Yoshida.  Emtst: Engineering the meta-theoryof  session  types.   In  Armin  Biere  and  David  Parker,  editors,Tools and Algorithms for theConstruction and Analysis of Systems, pages 278–285. Springer International Publishing, 2020.
4. Kohei Honda (1993): Types for Dyadic Interaction. In Eike Best, editor: CONCUR’93, Springer Berlin Heidelberg, Berlin, Heidelberg, pp. 509–523, doi:10.1007/3-540-57208-2_35.
5. Luís Caires, Frank Pfenning & Bernardo Toninho (2012): Towards Concurrent Type Theory. In: Proceedings of the 8th ACM SIGPLAN Workshop on Types in Language Design and Implementation, ACM, pp. 1–12, doi:10.1145/2103786.2103788.
6. Davide Sangiorgi & David Walker (2003): The Pi-Calculus: A Theory of Mobile Processes. Cambridge University Press.
7. Jean-Yves Girard (1993): On the Unity of Logic. Annals of Pure and Applied Logic 59(3), pp. 201–217, doi:10.1016/0168-0072(93)90093-S.
