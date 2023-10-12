#       Arrate Esteve, Claudia;
#       Gonz√°lez Montero, Sergio;
#       Mart√≠n Mart√≠n, V√≠ctor;
#       Miori Guti√©rrez, Alberto;
#       Olmedo Moreno, Juan Crist√≥bal;

def es_certificado_valido(N,L):
    
    # Comprobamos que N es un entero y L es una lista
    if (not isinstance(N,int)) or (not isinstance(L,list)): 
        return False
    
    # Si N < 2 no puede ser primo
    elif N < 2:
        return False
    
    # Comprobamos el caso en que 2 <= N <= 100, caso1
    elif N <= 100:    
        # Si N no es primo o L no es la lista válida devuleve False
        if not es_primo(N) or L != ['caso1',N]:  
            return False 

    # Comprobamos el caso en que  N > 100, caso2              
    elif N > 100:   
        # Si la lista tiene menos de 3 elementos o el primero no es 'caso2'
        # o el segundo N, devolverá False
        if len(L) < 3 or (L[0] != 'caso2') or (L[1] != N):
            return False  
        # Si el tercer elemento no es una lista y los elementos de ésta
        # correspondientes a pi, ai y xi no son enteros o certificado(pi)
        # no es una lista, devuelve False
        for i in range(2,len(L)):
            if ((not isinstance(L[i],list)) or (not isinstance(L[i][0],int))
            or (not isinstance(L[i][1],int)) or (not isinstance(L[i][2],list)) 
            or (not isinstance(L[i][3],int))): 
                return False 
        # Comprobamos ahora que el productorio de los pi^ai es igual a N-1
        n1 = 1
        for i in range(2,len(L)):       
           n1 *= pow(L[i][0],L[i][1]) 
        if n1 != N - 1:            
           return False
        # Comprobamos para los ai si cumplen el Test de primalidad de Lucas    
        for i in range(2,len(L)):                       
           if lucas(L[i][3],L[i][0],L[1]) == False:                   
              return False
        # Comprobamos que cada certificado(pi) en L es válido
        for i in range(2,len(L)):                            
           if es_certificado_valido(L[i][0],L[i][2]) == False: 
              return False                                
           
    # Si todo lo anterior se ha cumplido, el certificado será válido    
    return True


# Verifica si un núermo es primo
def es_primo(n): 
    primo = True
    if n == 2:
        primo = True
        return primo
    elif n % 2 == 0:
        primo = False
        return primo
    i = 3
    while i*i <= n:
        if n % i == 0:
            primo = False
            break
        i += 2
        
    return primo


# Comprueba que el entero x, cumple la condición 2 del test de primalidad de Lucas
# para un número N y p factor primo de N -1
def lucas(x,p,N): 
    return (pow(x,N-1,N) == 1) and (pow(x,(N-1)//p,N) != 1) 
    

# Cálculo de las variables globales
# L1 = certificado(3*2**189+1) 
# L2 = certificado(1477!+1)
import random
import time

#Crea un certificado sucinto de primalidad válido
def certificado(N): 
    if (2 <= N <= 100) and es_primo(N) :
        L = ["caso1",N]
    elif N > 100:
        n = N - 1
        L = ["caso2",N]
        for i in range(0,len(factorizar(n)[0])):
            L.append([factorizar(n)[0][i],factorizar(n)[1][i],
                  certificado(factorizar(n)[0][i]),lucas_busqueda(N,factorizar(n)[0][i])])
    else:
        # Caso auxiliar, en algún momento llevará a que devuelva False
        L = ["caso3",N]
    return L
 
# Crea una lista con dos listas:
# fact contiene los factores primos de N
# mult contiene las multiplicidades de la posición de fact correspondiente  
def factorizar(N): 
    fact = []      
    mult = []      
    i = 2
    
    while i * i <= N:
        m = 0
        while N % i == 0:
            N //= i
            m += 1
        if m > 0:
            fact.append(i)
            mult.append(m)
        i += 1
    if N > 1:
        fact.append(N)
        mult.append(1)
        
    return [fact, mult]

# Busca mediante el test de primalidad de Lucas los números enteros que 
# cumplen la condición 2) del teorema para el N dado (Primo o compuesto) 
def lucas_busqueda(N, p): 
    a = random.randint(1, N-1)      
    for i in range(1,100): 
        if (pow(a,N-1,N) == 1) and (pow(a,(N-1)//p,N) != 1): 
            return a
        else:
            a = random.randint(1, N-1)
            
# Calcula el factorial de un entero >= 1
def factorial(n):  
    i = 1
    f = 1
    while i <= n:
        f = f * i 
        i += 1 
    return f

#%%
l1 = 3 * 2**189 + 1 
l2 = factorial(1477) + 1
L1 = certificado(l1)
# L2 = certificado(l2)
inicio = time.time()
L2 = certificado(l2)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución del test: {tiempo_ejecucion//60} minutos y {tiempo_ejecucion%60} segundos \n")

#%%
inicio = time.time()
resultado = es_certificado_valido(l2,L2)
fin = time.time()
tiempo_ejecucion = fin - inicio
print(f"Tiempo de ejecución del test: {tiempo_ejecucion//60} minutos y {tiempo_ejecucion%60} segundos \n")
print(f"El certificado es {resultado}\n")