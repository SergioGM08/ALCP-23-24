#       Arrate Esteve, Claudia;
#       Gonzalez Montero, Sergio;
#       Martin Martin, Victor;
#       Miori Gutierrez, Alberto;
#       Olmedo Moreno, Juan Cristobal;

# {p primo impar, n >= 1; 0 <= a < p^n} 
# Buscamos alguna solucion de x^2 = a (mod p^n), lo haremos usando el Teorema de Hensel:
# x^2 = a (mod p^n) tiene solucion <=> x^2 = a (mod p) tiene solucion.
# Se comprueba que x^2 = a (mod p) tiene solucion, se busca con el algoritmo de 
# Tonelli-Shanks para despues construir la solucion de x^2 = a (mod p^n) usando la 
# demostracion del Teorema de Hensel

def sqrt_mod(a, p, n):
    # Si a es 0, 0^2 = 0 (mod p^n), la solucion unica es 0 (Ya que p es primo 
    # impar luego gcd(a,p) = 1 para 1 <= a <= p**n-1)
    # Si a es 1, 1^2 = 1 (mod p^n) y (-1)^2 = 1 (mod p^n)
    a_mod_pn = a%(p**n)
    if a_mod_pn == 0  or a_mod_pn == 1:
        return a_mod_pn
    
    # Si 2 <= a <= p^n-1 buscamos la solucion tal cual hemos explicado en la introduccion
    x = None
    # Caso en que a no es multiplo de p 
    if a%p != 0:
        
        if es_rest_cuad(a,p):
            x = tonelli_shanks(a,p)
            k = 2
            
            while k <= n:
                x = hensel(a,x,p,k)
                k += 1
                
    # Caso en que a es multiplo de p
    else:
        # Si a = b*p**u, gcd(p,b) = 1, y 1 <= u < n, entonces x**2 = a (mod p**n) 
        # tiene solucion sii u es par y b es resto cuadratico modulo p**n
        b, u = descomposicion(a,p)
        
        # Si gcd(b,p) = 1, p primo impar, n >= 1 y b un entero, entonces
        # b es resto cuadratico (mod p) sii a es resto cuadratico (mod p**n)
        if u < n and u%2 == 0 and es_rest_cuad(b, p): 
            # Calculamos la solucion de la siguiente forma:
            # x^2 = b*p^u (mod p^n) con u par y u < n. La transformamos:
            # (x/p^(u/2))^2 = b (mod p^(n-u))
            # Calculamos la solucion de x^2 = b (mod p^(n-u))
            # Y a ese resultado le multiplicamos por p^(u/2)
            y = sqrt_mod(b,p,n-u)
            x = y*p**(u//2)
    
    return x


# Para comprobar si a es resto cuadratico modulo p nos valemos
# de uno de los teoremas vistos en clase
def es_rest_cuad(a,p):
    return pow(a,(p-1)//2,p) == 1 


# Buscamos la solucion de x^2 = a (mod p), descomponiendo p como: p - 1 = d*2**s
# y encontramos pares (x,z) que cumplen ciertas condiciones, finalmente
# obteniendo una solucion de la ecuacion inicial
def tonelli_shanks(a,p):
    d, s = descomposicion_ts(p)
    z = pow(a,d,p)
    x = pow(a,(d+1)//2,p)
    w = busc_rest_no_cuad(p)
    i = 1
    
    while i < s:
        if pow(z,2**(s-(i+1)),p) == 1:
            i += 1
            
        else:
            t = pow(w,d*2**(i-1),p)
            x = (x*t)%p
            z = (z*t**2)%p
            i += 1
            
    return x 
        
        
# Funcion auxiliar que dado un numero p (Siempre van a ser primos impares) lo
# decompone de forma que p - 1 = d*2**s donde d es un entero impar y s >= 1        
def descomposicion_ts(p):
    n, s = p - 1, 0

    while n % 2 == 0:
        n //= 2
        s += 1
        
    return (n,s)


# Funcion auxiliar que dado un numero a entero y un numero p 
# (preferiblemente primo) te da la descomposicion a = b*p**u
def descomposicion(a,p): 
    u, b = 0, a
    
    while b % p == 0:
        b //= p
        u += 1
        
    return (b,u)
    

import random

# Funcion que nos permite buscar a en el intervalo [2,p-1]
# que no sea resto cuadratico modulo p
def busc_rest_no_cuad(p):
    
    w = random.randint(2,p-1)
    
    while es_rest_cuad(w,p):
        w = random.randint(2,p-1)
        
    return w

# Funcion que obtiene una solucion partiendo de una de Tonelli-Shanks, 
# levantando el exponente del modulo con la demostracion del teorema de Hensel
def hensel(a,x,p,k):
    w = ((x**2 - a)//p**(k-1))%(p**k)
    x_1 = inver_mul_mod(2*x,p**k)
    t = (-w*x_1) % (p**k)
    
    return (x + t*p**(k-1)) % (p**k)

# Funcion auxiliar para el c‡lculo del inverso modular
def inver_mul_mod(a, N):
    # Inicializamos los valores para el algoritmo de Euclides extendido
    r0, r1 = N, a       # Para gcd
    x0, x1 = 0, 1       # Para inverso multiplicativo

    while r1 != 0:
        cociente = r0 // r1
        r0, r1 = r1, r0 - cociente * r1
        x0, x1 = x1, x0 - cociente * x1

    # Aseguramos que el resultado sea positivo y menor que 'N'
    # ya que en Bezout puede no salir directamente de esta manera
    inverso = x0 % N
    
    return inverso

