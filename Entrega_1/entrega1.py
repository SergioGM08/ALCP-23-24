#Alumnos: 
#       Arrate Esteve, Claudia;
#       González Montero, Sergio; 
#       Martín Martín, Víctor;
#       Miori Gutiérrez, Alberto;
#       Olmedo Moreno, Juan Cristóbal;

def number2word(p,n):
    word = ''
    num = p - 1                                     # Ajustamos el número porque lo necesitamos para el correcto funcionamiento del algoritmo.
    k = n
    while k > 1:
          num_pal_let = 0
          for i in range(1,k+1):
              num_pal_let += 26**(i-1)              # Número total de palabras que empiezan por cualquiera de las 26 letras y de longitud desde 1 hasta k.
            
          if num%num_pal_let == 0:                  # Si p-1 es divisible entre num_pal_let previamente definido 
             word += chr((num//num_pal_let)+97)     # entonces a la palabra se le añade la letra que toca 
             break                                  # y se acaba el proceso.
            
          word += chr((num//num_pal_let)+97)        # Concatenación de letras transformando la división entera de num y num_pal_let a unicode.
          num = num%num_pal_let - 1                 # Restamos 1 al resto para el correcto funcionamiento del algoritmo en la siguiente iteración del bucle.
          k -= 1
    if k == 1:                                      # Caso base: palabras de longitud 1.
       word += chr(num+97)        
    return word



def word2number(w,n):
    num_pal_let = 0
    number = 0
    p = n                                           # Contador para acabar al leer el último caracter de w
    while p > n - len(w):
        if ord(w[n-p])-97 == 0:                     # Se obtiene el valor de unicode del caracter correspondiente.
            number += 1
            p -= 1
        else:
            for k in range(1,p+1,1):                    
                num_pal_let += 26**(k-1)                    
            number += (ord(w[n-p])-97)*num_pal_let + 1  # Sumamos al número el índice de la letra correspondiente por 
            num_pal_let = 0                             # num_pal_let definido igual que en la función anterior + 1 para el correcto funcionamiento del algoritmo.
            p -= 1       
    return number