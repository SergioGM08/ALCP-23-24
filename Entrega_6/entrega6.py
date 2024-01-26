# -*- coding: utf-8 -*-
#       Arrate Esteve, Claudia;
#       Gonzalez Montero, Sergio;
#       Martin Martin, Victor;
#       Miori Gutierrez, Alberto;
#       Olmedo Moreno, Juan Cristobal;


def encuentra_k(f,g):
    """
    f, g : list, polinomio
    returns k : int

    """
    largo = len(f) + len(g) + 1
    k = 0
    
    while 2**k < largo:
        k += 1
    
    return k

def remover_ceros(f):
    """
    f : lst, polinomio
    returns : f, lst; polinomio sin ceros redundantes
    """
    while f[-1] == 0:
        f.pop(-1)
    
    return f

def mult_pol_mod(f,g,p):
    """
    f, g : list, polinomio empezando por el término independiente, en (Z/pZ)[x]
    p : int, primo != 2
    returns : list, polinomio f*g, en (Z/pZ)[x], sin ceros redundantes
    """
    if f == [] or g == []:
        return []
    
    k = encuentra_k(f, g)
    n = 2**k
    f, g = f + [0]*(n-len(f)), g + [0]*(n-len(g)) # Acomoda f, g para llamar a ss
    f_por_g_modp_sin_ceros = remover_ceros(mult_ss_mod(f, g, k, p))
    
    return f_por_g_modp_sin_ceros

def sum_coord_a_coord(f, g, p):
    """
    f, g : lst; polinomios
    p : int, primo
    """
    return list(map(lambda x, y: (x+y)%p, f, g))


def rest_coord_a_coord(f, g, p):
    """
    f, g : lst, polinomios
    p : int, primo
    """
    return list(map(lambda x, y: (x-y)%p, f, g))


def mult_escalar(c, f, p):
    """
    c, p : int; escalar, primo
    f : lst; polinomio
    """
    return list(map(lambda x: (x*c)%p, f))

def particion(f,n1):
    """
    f : lst; polinomio
    n1 : int
    f1 : lst; polinomio fragmentado
    """
    f1 = []
    parte = []
    
    for i in f: 
        if len(parte) < n1:
            parte.append(i)
        
        else:
            f1.append(parte + [0]*n1)
            parte = [i]

    f1.append(parte + [0]*n1)
    return f1

def union(f, p):
    """
    f : lst; polinomio
    p : int; primo
    """
    n1, n2 = len(f[0])//2,  len(f)
    f1 = [0] * (n1 * n2)

    for i in range(n1):
        f1[i] = (f[0][i] - f[n2 - 1][i + n1]) % p
        
    for j in range(n2 - 1):
        ind = (j + 1) * n1
        for i in range(n1):
            f1[i + ind] = (f[j][i + n1] + f[j + 1][i]) % p
    
    return f1

# Funcion auxiliar para el calculo del inverso modular
def inver_mul_mod(a, N):
    """
    a : int; a calcular su inverso
    N : int; módulo
    returns inverso : int; inverso de a mod N

    """
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

def permuta(f, n_pos, p):
    """
    f : lst; polinomio
    n_pos : int; número de posiciones a desplazar
    p : int; primo
    returns : lst; polinomio permutado
    """
    if n_pos == 0:
        return f
    
    if n_pos == 1:
        return [((-1)*f[-1]) % p] + f[0:len(f)-1]

    if n_pos > 1:
        count = 0
        while count < n_pos:
            f = [((-1)*f[-1]) % p] + f[0:len(f)-1]
            count += 1
            
        return f
    
    if n_pos < 0:
        count = 0
        while count < abs(n_pos):
            f = f[1:] + [((-1)*f[0])%p]
            count += 1
            
        return f
    
# Algoritmo de Cooley-Tuckey reversionado. exp_raiz grado
# la raíz n-ésima, donde n es el grado del polinomio cociente
def fft(f, exp_raiz, p):
    """
    f : lst; polinomio
    exp_raiz : int
    p : int; primo
    """
    n = len(f)
    
    if n == 1:
        return f
    
    f_even = [0] * (n//2)
    f_odd = [0] * (n//2)
    
    for i in range(n//2):
        f_even[i] = f[2*i]
        f_odd[i] = f[2*i+1]
        
    a_even = fft(f_even, exp_raiz*2, p)
    a_odd = fft(f_odd,exp_raiz*2, p)
    a = [0]*n
    
    for i in range(n//2):
        a[i] = sum_coord_a_coord(a_even[i], permuta(a_odd[i], exp_raiz*i, p), p)
        a[i+n//2] = rest_coord_a_coord(a_even[i], permuta(a_odd[i], exp_raiz*i, p), p)
    
    return a

def mult_ss_mod(f,g,k,p):
    """
    f, g : list, polinomio empezando por el término independiente, tamaño 2**k
    k : int,  k = 0, 1, 2; exponente de x**(2**k)
    p : int, primo != 2
    returns : list, polinomio f*g en (Z/pZ)[x]/<x^(2^k)+1>
    """
    # Casos base k = 0, 1, 2
    if k == 0: # deg(f,g) < n = 2^0
        result = [(f[0]*g[0])%p]
    
    if k == 1: # deg(f,g) < n = 2^1, cocientado (x^2 + 1)
        result = [(f[0]*g[0] - f[1]*g[1])%p, (f[0]*g[1] + f[1]*g[0])%p]
    
    if k == 2: # deg(f,g) < n = 2^2, cocientado (x^4 + 1)
        deg4 = f[1]*g[3] + f[2]*g[2] + f[3]*g[1]
        deg5 = f[2]*g[3] + f[3]*g[2]
        deg6 = f[3]*g[3]
        result = [
                    (f[0]*g[0] - deg4)%p,  # Grado 0
                    (f[0]*g[1] + f[1]*g[0] - deg5)%p,  # Grado 1
                    (f[0]*g[2] + f[1]*g[1] + f[2]*g[0] - deg6)%p,  # Grado 2
                    (f[0]*g[3] + f[1]*g[2] + f[2]*g[1] + f[3]*g[0])%p  , # Grado 3
                    ]
        
    else:
        if k%2 == 0:
            k1 = k//2
            k2 = k//2
            
        else:
            k1 = (k-1)//2
            k2 = (k+1)//2
    
        n2 = 2**k2
        n1 = 2**k1
    
        f1, g1 = particion(f, n1), particion(g,n1)
        nf, ng = [], []
        n_pos = (2*n1//n2)
        
        for i in range(n2):
            nf.append(permuta(f1[i], i*n_pos, p))
            ng.append(permuta(g1[i], i*n_pos, p))
                        
        ff = fft(nf, (4*n1)//n2, p)
        fg = fft(ng, (4*n1)//n2, p)
        pol_ss = [0]*n2
            
        for i in range(n2):
            pol_ss[i] = mult_ss_mod(ff[i], fg[i], k1+1, p)
                
        f_pol_ss = fft(pol_ss, -2*n_pos, p)
        inverso = inver_mul_mod(n2, p)
        pol_inv = []*len(f_pol_ss)
                
        for pol in f_pol_ss:
            pol_inv.append(mult_escalar(inverso, pol, p))
                    
        h = [0]*n2
        for i in range(n2):
            h[i] = permuta(pol_inv[i], -i*n_pos, p)
                        
        result = union(h, p)
    
    return result
    