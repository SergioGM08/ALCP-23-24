#Alumnos: 
#       Arrate Esteve, Claudia;
#       González Montero, Sergio; 
#       Martín Martín, Víctor;
#       Miori Gutiérrez, Alberto;
#       Olmedo Moreno, Juan Cristóbal;

def min_suma_casillas(n,m,a):
    
    # Crea una tabla para almacenar la suma mínima de un camino para llegar a cada celda de la matriz.
    sumsTable = [[0 for x in range(m)] for x in range(n)]

    # Inicializa los valores de los márgenes superior e izquierdo de la tabla.
    sumsTable[0][0] = a[0][0]
    for i in range(1, n):
        sumsTable[i][0] = sumsTable[i - 1][0] + a[i][0]
    for j in range(1, m):
        sumsTable[0][j] = sumsTable[0][j - 1] + a[0][j]

    # Llenamos la tabla usando programación dinámica para eficientar procesos.
    for i in range(1, n):
        for j in range(1, m):
            sumsTable[i][j] = min(sumsTable[i - 1][j], sumsTable[i][j - 1]) + a[i][j]

    # Devuelve la suma mínima de un camino para llegar a la esquina inferior derecha de la matriz.
    return sumsTable[n - 1][m - 1]
