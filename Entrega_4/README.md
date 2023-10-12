# ALCP: Entrega 4
## Práctica 4:
Un certificado sucinto de primalidad de un entero N≥2 es una lista L=certificado(N) tal que:
Si N es un primo entre 2 y 100 (inclusive), entonces $L=["caso1",N]$.  
Si N es mayor que 100 y $N−1=p_1^{a_1}⋯p_r^{a_r}$, con $p_1 < p_2 < ... < p_r$ primos distintos y los $a_i \geq 1$, entonces 
$$L=["caso2",N,[p_1,a_1,certificado(p_1),x_1],...,[p_r,a_r,certificado(p_r),x_r]]$$
donde $1 \leq x_i < N, x_i^{N−1} \equiv 1 (mod N)$ y $x_i^{(N−1)/p_i}≢ 1(mod N)$.

Implementar en Python3 la función es_certificado_valido(N,L) que dado un entero N≥2 y una lista L, determine si L es un certificado sucinto de primalidad de N. Todo el código debe estar en el fichero entrega4.py. La función debe comprobar que L tiene el formato correcto y que se cumplen todas las condiciones. Notar que por el teorema de Lucas, solo los primos N≥2 pueden tener un certificado válido. El código tiene que definir también dos variables globales L1 y L2 que tengan certificados sucintos de primalidad de 3⋅2^189+1 y 1477!+1, respectivamente. Fecha límite: 15/oct/2023, 23:59.

Nota 1: NO hay que implementar la función certificado( n ), ya que esto requeriría factorizar números de tamaño posiblemente muy grande.

Nota 2: Se pueden incluir código para crear los certificados L1 y L2, o bien, generarlos externamente e incluirlos cortando y pegando en la entrega.

Nota 3: Evidentemente, es imposible construir un certificado válido de un número compuesto, pero es no implica que la función es_certificado_valido(N,L) no será invocado con N compuesto o con L una lista inválida. La función debe comprobar la consistencia del certificado L con el valor de N y devolver True o False.

### Correo de Martín:
Hola Victor,

Debes comprobar que L cumple todo lo pedido, es decir,

(1) que es una lista
(2) que tiene la longitud requerida
(3) que las entradas son del tipo correcto
(4) que las entradas tienen el valor correcto
(5) que se cumples todas las identidades algebraicas
...

y eso debes hacerlo "recursivamente", dada la estructura
de los certificados L.

Saludos,
Martín.
