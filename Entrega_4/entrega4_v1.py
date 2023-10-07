#       Arrate Esteve, Claudia;
#       González Montero, Sergio; 
#       Martín Martín, Víctor;
#       Miori Gutiérrez, Alberto;
#       Olmedo Moreno, Juan Cristóbal;

def fact_mul(N):
    fact = [0]
    mult = [0]
    i, j = 2, 1
    while i <= (N-1)//i:
        print(f"N = {N}")
        if N%i == 0:
            if fact[j] != i:
                fact.append(i)
                mult.append(1)
            else:
                mult[j] += 1 
            N //= i
        else:
            i += 1 
            j += 1 
    return [fact, mult]

def factorizar_numero(N):
    factores_primos = []
    multiplicidad = []
    divisor = 2  # Empezamos con el divisor m�s peque�o

    while N > 1:
        multiplicidad_actual = 0

        while N % divisor == 0:
            N //= divisor
            multiplicidad_actual += 1

        if multiplicidad_actual > 0:
            factores_primos.append(divisor)
            multiplicidad.append(multiplicidad_actual)

        divisor += 1  # Pasamos al siguiente divisor

    return list(zip(factores_primos, multiplicidad))
    
def certificado(N):
    if 2 <= N <= 100:
        L = ["caso1", N]
    else:
        L = ["caso2, N, [pi,ai,certificado(pi),xi]"]
    
def es_certificado_valido(N, L):
    c = L == certificado(N)
    return c
        