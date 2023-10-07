def es_certificado_valido(N, L):
    """
    Determina si L es un certificado sucinto de primalidad de N.

      Args:
          N: Un entero N≥2.
          L: Una lista L=certificado(N).

      Returns:
          True si L es un certificado sucinto de primalidad de N, False en caso contrario.
    """
    # Función auxiliar para comprobar la primalidad de los N<=100
    def esprimo(N):
        if N < 2:
            return False
        for i in range(2, int(N**0.5) + 1):
            if N % i == 0:
                return False
        return True


    # Comprobar que N≥2
    if N < 2:
        return False

    # Comprobar el formato de L
    if len(L) < 2 or L[0] != "caso1" and L[0] != "caso2":
        return False

    # Comprobar el caso 1
    if L[0] == "caso1":
        if N < 101 and L[1]==N and esprimo(N):
            return True
        else:
            return False

    # Comprobar el caso 2
    if L[0] == "caso2":

    # Comprobar que N-1 es el producto de primos elevados a potencias:
        prod = 1
        for pi, ai, _, _ in L[2:]:
            prod = prod* pi**ai
            
        if N-1 != prod:
            return False

    # Comprobar que x_i^(N−1) ≡ 1 (mod N) y x_i^((N−1)/p_i)≢ 1 (:mon N)
        for pi, ai, _, xi in L[2:]:
            if pow(xi, N - 1, N) != 1:
                return False
            if pow(xi, (N - 1) // pi, N) == 1:
                return False
        return True
    # Comprobar que los certificados de los primos son válidos:
        for pi, _, cert, xi in L[2:]:
            if not(es_certificado_valido(pi, cert)):
                return False
    # Si se llega a este punto, L no tiene el formato correcto:
    return False
