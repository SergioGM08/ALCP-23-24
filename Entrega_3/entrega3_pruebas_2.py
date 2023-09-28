# Alumnos:
#       Arrate Esteve, Claudia;
#       González Montero, Sergio;
#       Martín Martín, Víctor;
#       Miori Gutiérrez, Alberto;
#       Olmedo Moreno, Juan Cristóbal;

# Problema 3.7. Reimplementar el algoritmo gcd binario(x,y) del programa gcds.py
# del tema #2 para x, y ≥ 0 representados por listas de d´ıgitos (reducidas) y
# demostrar que su complejidad es O(n2), donde n = len(x)+len(y).
# Parte del ejercicio consiste en implementar la función mul2(x) que calcule
# el doble de un entero x ≥ 0.
# También se deben implementar las funciónes auxiliares mul2(x) y div2(x) que
# calculen el doble y la mitad de x, con la representación de listas de dígitos.
# Se espera que las funciones puedan manejar valores de len(x+y) hasta 10000.
import random
import time
import math


def gcd_binario_nuevo(x, y):
    n = len(x)
    m = len(y)
    xespar = x[0] % 2 == 0
    yespar = y[0] % 2 == 0

    if x[n-1] == 0:
        t = y
    elif y[m-1] == 0:
        t = x
    elif xespar and yespar:
        t = mul2(gcd_binario_nuevo(div2(x), div2(y)))
    elif xespar:
        t = gcd_binario_nuevo(x/2, y)
    elif yespar:
        t = gcd_binario_nuevo(x, y/2)
    elif n > m:
        t = gcd_binario_nuevo(x, div2(x-y))
    else:
        t = gcd_binario_nuevo(x, div2(x-y))
    return t


def mul2(x):
    c = 0                               # Acarreo
    doble_x = []

    for digito in x:
        doble = digito * 2 + c          # El doble más el acarreo
        # Añadimos la cifra en el lugar correspondiente
        doble_x.append(doble % 10)
        c = doble // 10

    while c > 0:
        doble = digito * 2 + c
        doble_x.append(c % 10)
        c //= 10

    return doble_x


num_aleat = [random.randint(0, 9) for _ in range(10000)]

# Complejidad en tiempo
inicio = time.time()
resultado = mul2(num_aleat)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución de mul2: {tiempo_ejecucion} segundos \n")


def div2(x):
    c = 0                                              # Acarreo
    mitad_x = []

    for digito in x:
        # La mitad más el acarreo
        mitad = math.floor(digito * (1/2) + c)
        # Añadimos la cifra en el lugar correspondiente
        mitad_x.append(mitad % 10)
        c = mitad // 10

    while c > 0:
        mitad = math.floor(digito * (1/2) + c)
        mitad_x.append(c % 10)
        c //= 10

    return mitad_x

# Complejidad en tiempo
inicio = time.time()
resultado = div2(num_aleat)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución de div2: {tiempo_ejecucion} segundos \n")
