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

def gcd_binario_tail_rec_lst(x,y):    # (x,y) != (0,0)
    m = [1]
    while x != [] and y != []:      # x e y distintos de 0
        if x[-1] < 0:
            x[-1] *= -1
        if y[-1] < 0:
            y[-1] *= -1
        xespar = x[0]%2 == 0
        yespar = y[0]%2 == 0
        if xespar and yespar:
            #print("If 1")
            m = mul2(m)               # aquí acumulamos las potencias de 2
            x = div2(x)
            y = div2(y)
        elif xespar:
            #print("elif 1")
            x = div2(x)
        elif yespar:
            #print("elif 2")
            y = div2(y)
        elif x_mayor_que_y(x, y) == 1:
            #print("elif 3")
            x = div2(restar(x,y))
        else:
            #print("else")
            y = div2(restar(y,x))
    if x == []:                    # caso base: gcd(0,y)=y
        #print("Caso base 1")
        m = multiplicar_karatsuba(m, y)
    else:                         # caso base: gcd(x,0)=x
        #print("caso base 2")
        m = multiplicar_karatsuba(m, x)
    return m

def multiplicar_karatsuba(a, b):
    n = len(a)
    m = len(b)
    
    if n < m:
        a, b = b, a
        n, m = m, n
    
    if m <= 10:
        prod = multiplicar(a, b)
    elif m <= n // 2:
        c0 = multiplicar_karatsuba(a[:n // 2], b)
        c1 = multiplicar_karatsuba(a[n // 2:], b)
        c1 = sumar(c1, c0[n // 2:])
        
        if len(c0) < n // 2:
            c0 += [0] * (n // 2 - len(c0))
        
        prod = c0[:n // 2] + c1
    else:
        c0 = multiplicar_karatsuba(a[:n // 2], b[:n // 2])
        c2 = multiplicar_karatsuba(a[n // 2:], b[n // 2:])
        s1 = sumar(a[:n // 2], a[n // 2:])
        s2 = sumar(b[:n // 2], b[n // 2:])
        c1 = multiplicar_karatsuba(s1, s2)
        s3 = sumar(c0, c2)
        c1 = restar(c1, s3)
        c1 = sumar(c1, c0[n // 2:])
        c2 = sumar(c2, c1[n // 2:])
        
        if len(c0) < n // 2:
            c0 += [0] * (n // 2 - len(c0))
        
        if len(c1) < n // 2:
            c1 += [0] * (n // 2 - len(c1))
        
        prod = c0[:n // 2] + c1[:n // 2] + c2
    
    remover_ceros(prod)
    return prod

def multiplicar(a, b):
    # a, b son listas de dÃ­gitos "reducidas"
    n = len(a)
    m = len(b)
    c = [0] * (n + m)
    for i in range(n):  # i = 0, 1, ..., n - 1
        x = 0
        for j in range(m):  # j = 0, 1, ..., m - 1
            x = c[i + j] + a[i] * b[j] + x
            c[i + j] = x % 10
            x //= 10
        c[i + m] = x
    remover_ceros(c)
    return c

def sumar(a, b):
    # a, b son listas de dÃ­gitos "reducidas"
    n = len(a)
    m = len(b)

    # Nos aseguramos de que a sea el mÃ¡s largo
    if n < m:
        b, a = a, b
        n, m = m, n

    c = [0] * (n + 1)  # reservamos espacio suficiente para la suma
    x = 0  # x es el acarreo, que inicialmente es 0
    i = 0

    while i < m:  # i = 0, 1, ..., m - 1
        x = a[i] + b[i] + x
        c[i] = x % 10
        x //= 10
        i += 1

    while i < n:  # i = m, m + 1, ..., n - 1
        x = a[i] + x
        c[i] = x % 10
        x //= 10
        i += 1

    c[n] = x  # guardamos el Ãºltimo acarreo

    return c

def mul2(x):
    # print("He entrado a mul2")
    # print(f"El número es {x}")
    c = 0                                               # Acarreo
    doble_x = []                                        # Lista vacía para almacenar el resultado
    
    for digito in x:
        doble = digito * 2 + c                          # Multiplicamos el dígito por 2 y sumamos el acarreo
        doble_x.append(doble % 10)                      # Agregamos al final de la lista la cifra de las unidades
        c = doble // 10                                 # Actualizamos el acarreo para el siguiente dígito
        
    if c > 0:                                           # Si aún hay un acarreo pendiente
        doble_x.append(c)                               # Agregamos al final de la lista la cifra correspondiente

    return doble_x

def div2(a):
    n = len(a)
    q = [0]*n # Cociente
    i = n-1
    x = 0
    if a == []:
        return []
    while i >= 0:
        y = 10*x + a[i] # x es el resto, y el número a dividir
        q[i] = y//2
        x = y%2
        i -= 1
    if q[n-1] == 0:
        del q[n-1]
    return q

def restar(a, b):
    # print(f"He entrado a restar {a} - {b}")
    # a, b son listas de dí­gitos "reducidas"
    n = len(a)
    m = len(b)

    # # si se nos asegura que la función es llamada con a >= b, las
    # # siguientes dos líneas son innecesarias
    # if n < m:
    #     return

    c = [0] * n  # crear c = lista de n ceros
    x = 0  # inicializar el acarreo x a cero
    i = 0
    while i < m:  # i=0, 1, ..., m - 1
        # print(f"Estoy en restar; i = {i}; m = {m}")
        # print(f"a = {a}; b = {b}\n")
        x = a[i] - b[i] + x
        c[i] = x % 10
        x //= 10
        i += 1

    while i < n:  # i = m, m + 1, ..., n - 1
        x = a[i] + x
        c[i] = x % 10
        x //= 10
        i += 1

    remover_ceros(c)
    return c

def x_mayor_que_y(x,y):                                 # Decide si x es mayor que y
    # print("He entrado a x_mayor_que_y")
    # print(f"x = {x}\ny = {y}\n")
    n, m = len(x), len(y)
    i = n-1
    if n > m:                                           # Compara las longitudes
        return 1                                        # aprovechando que son "reducidas"
    elif n < m:
        return -1
    elif n == m:                                        # A igualdad de longitudes compara
        while i >= 0:                                   # la cifra más significativa
            if x[i] > y[i]:
                return 1
            elif x[i] < y[i]:
                return 0
            else:                                       # Son iguales hasta la última posición
                i -= 1
                if i == 0 and x[0] == y[0]:
                    return 0

def remover_ceros(a):                                                   # De lista a lista reducida
    # a = lista de dí­gitos decimales                                    # Ej: [1,2,3,0] --> [1,2,3]
    n = len(a)
    while n >= 1 and a[n - 1] == 0:
        n -= 1
    del a[n:]
    return a

x = [random.randint(0, 9) for _ in range(10000)]
y = [random.randint(0, 9) for _ in range(10000)]
x = remover_ceros(x)
y = remover_ceros(y)

# Complejidad en tiempo
inicio = time.time()
resultado = gcd_binario_tail_rec_lst(x, y)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución de test: {tiempo_ejecucion/60} minutos \n") 