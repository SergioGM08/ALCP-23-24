#       Arrate Esteve, Claudia;
#       González Montero, Sergio;
#       Martín Martín, Víctor;
#       Miori Gutiérrez, Alberto;
#       Olmedo Moreno, Juan Cristóbal;

def gcd_binario(x,y):                       # (x,y) != (0,0)
    m = [1]
    while x != [] and y != []:              # x e y distintos de 0
        if x[-1] < 0:
            x[-1] *= -1
        if y[-1] < 0:
            y[-1] *= -1
        xespar = x[0]%2 == 0                # Comprobamos paridad
        yespar = y[0]%2 == 0
        if xespar and yespar:
            m = mul2(m)                     # Aquí acumulamos las potencias de 2
            x = div2(x)
            y = div2(y)
        elif xespar:                        
            x = div2(x)
        elif yespar:
            y = div2(y)
        elif x_mayor_que_y(x, y) == 1:      # x es mayor que y
            x = div2(restar(x,y))
        else:                               # x es menor o igual que y
            y = div2(restar(y,x))
    if x == []:                             # Caso base: gcd(0,y)=y
        m = multiplicar_karatsuba(m, y)
    elif y == []:                           # Caso base: gcd(x,0)=x
        m = multiplicar_karatsuba(m, x)
    return m


def multiplicar_karatsuba(a, b):            # Algoritmo de multiplicar de Karatsuba visto en clase
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


def multiplicar(a, b):                      # a, b son listas de dígitos "reducidas"
    n = len(a)
    m = len(b)
    c = [0] * (n + m)
    for i in range(n):                      # i = 0, 1, ..., n - 1
        x = 0
        for j in range(m):                  # j = 0, 1, ..., m - 1
            x = c[i + j] + a[i] * b[j] + x
            c[i + j] = x % 10
            x //= 10
        c[i + m] = x
    remover_ceros(c)
    return c


def sumar(a, b):                            # a, b son listas de dígitos "reducidas"
    n = len(a)
    m = len(b)

    if n < m:                               # Nos aseguramos de que a sea el más largo
        b, a = a, b
        n, m = m, n

    c = [0] * (n + 1)                       # reservamos espacio suficiente para la suma
    x = 0                                   # x es el acarreo, que inicialmente es 0
    i = 0

    while i < m:                            # i = 0, 1, ..., m - 1
        x = a[i] + b[i] + x
        c[i] = x % 10
        x //= 10
        i += 1

    while i < n:                            # i = m, m + 1, ..., n - 1
        x = a[i] + x
        c[i] = x % 10
        x //= 10
        i += 1

    c[n] = x                                # guardamos el último acarreo
    return c


def mul2(x):
    c = 0                             # Acarreo
    doble_x = []                      # Lista vacía para almacenar el resultado
    
    for digito in x:
        doble = digito * 2 + c        # Multiplicamos el dígito por 2 y sumamos el acarreo
        doble_x.append(doble % 10)    # Agregamos al final de la lista la cifra de las unidades
        c = doble // 10               # Actualizamos el acarreo para el siguiente dígito
        
    if c > 0:                         # Si c > 0 hay un acarreo pendiente
        doble_x.append(c)             # Agregamos al final de la lista la cifra correspondiente

    return doble_x


def div2(a):
    n = len(a)
    q = [0]*n                         # Cociente
    i = n-1
    x = 0
    if a == []:
        return []
    while i >= 0:
        y = 10*x + a[i]               # x es el resto e y el número a dividir
        q[i] = y//2
        x = y%2
        i -= 1
    if q[n-1] == 0:
        del q[n-1]
    return q


def restar(a, b):   # a, b son listas de dígitos "reducidas"
    n = len(a)
    m = len(b)

    c = [0] * n                                 # Crear lista de n ceros
    x = 0                                       # Inicializar el acarreo x a cero
    i = 0
    while i < m:                                # i = 0, 1, ..., m - 1
        x = a[i] - b[i] + x
        c[i] = x % 10
        x //= 10
        i += 1

    while i < n:                                # i = m, m + 1, ..., n - 1
        x = a[i] + x
        c[i] = x % 10
        x //= 10
        i += 1

    remover_ceros(c)
    return c


def x_mayor_que_y(x,y):                           # Decide si x es mayor que y
    n, m = len(x), len(y)
    i = n-1
    if n > m:                                     # Compara las longitudes de x e y
        return 1                                  # aprovechando que son "reducidas"
    elif n < m:
        return -1
    elif n == m:                                  # A igualdad de longitudes compara
        while i >= 0:                             # la siguiente cifra más significativa
            if x[i] > y[i]:
                return 1
            elif x[i] < y[i]:
                return -1
            else:                                 
                i -= 1
                if i == 0 and x[0] == y[0]:       # Son iguales dígito a dígito, luego x == y
                    return 0


def remover_ceros(a):                   # Dada una lista que representa un número                                                                              
    n = len(a)                          # elimina los 0 innecesarios de la lista
    while n >= 1 and a[n - 1] == 0:
        n -= 1
    del a[n:]
    return a