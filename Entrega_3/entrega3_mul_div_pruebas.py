#       Arrate Esteve, Claudia;
#       Gonz√°lez Montero, Sergio; 
#       Mart√≠n Mart√≠n, V√≠ctor;
#       Miori Guti√©rrez, Alberto;
#       Olmedo Moreno, Juan Crist√≥bal;

# Problema 3.7. Reimplementar el algoritmo gcd binario(x,y) del programa gcds.py
# del tema #2 para x, y ‚â• 0 representados por listas de d¬¥ƒ±gitos (reducidas) y
# demostrar que su complejidad es O(n2), donde n = len(x)+len(y).
# Parte del ejercicio consiste en implementar la funci√≥n mul2(x) que calcule
# el doble de un entero x ‚â• 0.
# Tambi√©n se deben implementar las funci√≥nes auxiliares mul2(x) y div2(x) que
# calculen el doble y la mitad de x, con la representaci√≥n de listas de d√≠gitos.
# Se espera que las funciones puedan manejar valores de len(x+y) hasta 10000.

import random
import time
import math

# Lista de n√∫meros aleatorios de 10000 elementos
num_aleat = [random.randint(0, 9) for _ in range(10000)]


def mul2(x):
    c = 0                                               # Acarreo
    doble_x = []                                        # Lista vac√≠a para almacenar el resultado
    
    for digito in x:
        doble = digito * 2 + c                          # Multiplicamos el d√≠gito por 2 y sumamos el acarreo
        doble_x.append(doble % 10)                      # Agregamos al final de la lista la cifra de las unidades
        c = doble // 10                                 # Actualizamos el acarreo para el siguiente d√≠gito
        
    if c > 0:                                           # Si a√∫n hay un acarreo pendiente
        doble_x.append(c)                               # Agregamos al final de la lista la cifra correspondiente

    return doble_x


# Complejidad en tiempo
inicio = time.time()
resultado = mul2(num_aleat)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución de mul2: {tiempo_ejecucion} segundos \n")

### OJO! LA LISTA ORIGINAL SE DA LA VUELTA POR EL REVERSE, NO LOGRO DEJARLA TAL CUAL
### div2() creo que se puede eliminar del todo

def div2(x):                                            # Funciona pero va m√°s lento que la plus
    c = 0                                               # Acarreo
    mitad_x = []
    x.reverse()                                         # Para aprovechar la estructura de mul2()
    #print(x)                                           # es necesario revertir la lista
    for digito in x:
        mitad = math.floor((digito+c*10)*(1/2))         # La mitad de digito m√°s el acarreo hecho decena, si hubiera
        # print (f"La mitad de {digito} es {mitad}")
        mitad_x = [mitad] + mitad_x                     # A√±adimos la cifra al principio de la lista
        # print(f"He a√±adido {mitad%10}")
        if digito % 2 == 1:                             # Si d√≠gito es impar nos llevamos una de acarreo
            c = 1
        else:                                           # Si d√≠gito es par no llevamos acarreo
            c = 0

    return mitad_x

# Complejidad en tiempo
inicio = time.time()
resultado = div2(num_aleat)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución de div2: {tiempo_ejecucion} segundos \n")

def div2_plus(x):
    c = 0                                               # Acarreo
    mitad_x = []
    x_replica = x[::-1]                                 # Para aprovechar la estructura de mul2()
                                                        # es necesario revertir la lista replicada
    for digito in x_replica:                            
        if digito % 2 == 1:                             # Si dígito es impar nos llevamos una de acarreo
            c = 1
        else:                                           # Si dígito es par no llevamos acarreo
            c = 0
        mitad = (digito+c*10)//2                        # La mitad de digito más el acarreo hecho decena, si hubiera
        mitad_x = [mitad] + mitad_x                     # Añadimos la cifra al principio de la lista
            
    return mitad_x

# Complejidad en tiempo
inicio = time.time()
resultado = div2_plus(num_aleat)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución de div2_plus: {tiempo_ejecucion} segundos \n")

def div2_clase(a):
    n = len(a)
    q = [0]*n # Cociente
    i = n-1
    x = 0
    while i >= 0:
        y = 10*x + a[i] # x es el resto, y el número a dividir
        q[i] = y//2
        x = y%2
        i -= 1
    if q[n-1] == 0:
        del q[n-1]
    return q

# Complejidad en tiempo
inicio = time.time()
resultado = div2_clase(num_aleat)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución de div2_clase: {tiempo_ejecucion} segundos \n")


def lst2num(l):                                                         # Transforma una lista en un n√∫mero entero
    exp = 0                                                             # Ej: [1,2,3] --> 321
    result = 0
    for i in l:
        result += i*10**exp
        exp += 1
    return result

def remover_ceros(a):                                                   # De lista a lista reducida
    # a = lista de d√≠¬≠gitos decimales                                    # Ej: [1,2,3,0] --> [1,2,3]
    n = len(a)
    while n >= 1 and a[n - 1] == 0:
        n -= 1
    del a[n:]
    return a

def test():
    limit = 1000
    equal = True
    count = 1
    print(f"Test ha comenzado con límite {limit}")
    while equal:
        num_aleat = [random.randint(0, 9) for _ in range(10000)]        # Lista aleatoria de longitud 10000
        num_aleat = remover_ceros(num_aleat)                            # Se convierte a lista reducida
        if (2*lst2num(num_aleat)) != lst2num(mul2(num_aleat)):          # Compara mult2() convirti√©ndo a n√∫mero
            print(f"Ha fallado en mul2 la entrada {num_aleat}")
            print(f"count {count}\n")
            equal = False
        elif lst2num(num_aleat)//2 != lst2num(div2_clase(num_aleat)):    # Compara div2_plus() convirtiendo a n√∫mero
            print(f"Ha fallado en div2 la entrada {num_aleat}")
            print(f"count {count}\n")
            equal = False
        count += 1
        
        if count == limit:                                              # No ha encontrado una desigualdad
            print(f"Count {count}\n")                                   # y el contador ha llegado al l√≠mite
            break

# Complejidad en tiempo
inicio = time.time()
resultado = test()
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución de test: {tiempo_ejecucion/60} minutos \n")              
        
    
    
