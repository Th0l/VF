from z3 import *
import numpy as np

'''
Antes de começar o parse, vai-se definir a função que escreve num ficheiro o resultado
'''
def writeTofile(r,Xa,altura,largura,somaL,somaC):
    f = open("solucao.txt", "w")

    ca = 0
    cl = 0
    while(ca < altura):
        strToWrite = "linha" + str(ca+1) +": "

        while(cl < largura):
            if(cl > 0):
                strToWrite = strToWrite + " -+- "
            strToWrite = strToWrite + str(r[ca][cl])
            cl+=1

        strToWrite = strToWrite + " = " + str(somaL[ca]) + "\n"
        f.write(strToWrite)

        ca+=1
        cl = 0

    strToWrite2 = "---- "
    while(cl < largura):
        if(cl > 0):
            strToWrite2 = strToWrite2 + " - "
        strToWrite2 = strToWrite2 + str(somaC[cl])

        cl+=1

    strToWrite2 = strToWrite2 + "\n"
    f.write(strToWrite2)

    print_matrix(r)

'''
Condição Inicial para ver se argumentos estão ser passados corretamente
'''
if(len(sys.argv) <= 1):
    print("Por favor forneça ficheiro a resolver.")
    exit()
elif(len(sys.argv) > 2):
    print("Demasiados argumentos.")
    exit()

'''
Buscar o nome do ficheiro aos argumentos
'''
nomeFicheiro = sys.argv[1]
toSolve = open(nomeFicheiro,"r")
'''
vai buscar todas as linhas do ficheiro e mete numa
espécie de array
'''
lines = toSolve.readlines()

altura = len(lines) - 2
largura = int( (len(lines[0].strip()) - 3) / 2 )
'''
init das estruturas para guardar
'''
somaLinhas = np.zeros(altura)
somaColunas = np.zeros(largura)
tup = ()

'''
Passar a informação do txt para as matrizes
'''
count = 0
position = 0
for line in lines:
    if(count > 0 and count < (altura + 1)):
        tempSTR = (line.strip())[2:len(line.strip()):1]
        tempARR = tempSTR.split()
        size = len(tempARR)

        linha = tempARR
        soma = tempARR[largura]
        del linha[largura:]

        tup = tup + (tuple(map(int,linha)),)
        somaLinhas[position] = soma
        position+=1

    if(count == altura + 1):
        tempSTR = (line.strip())[2:len(line.strip())-1:1]
        tempARR = tempSTR.split()
        count2 = 0
        while(count2 < largura):
            somaColunas[count2] = tempARR[count2]
            count2+=1

    count+=1
'''
Começar a fazer a construção do modelo
'''
# O tabuleiro vai ser i*j, logo vai se fazer as variaveis com o seu nome a ser a posição
X = [ [ Int("x_%s_%s" % (i+1, j+1)) for j in range(largura) ]
      for i in range(altura) ]

# Cada celula apenas tem um valor entre (1 ----- m*n)
MxN = largura * altura
cells_c  = [ And(1 <= X[i][j], X[i][j] <= MxN)
             for i in range(altura) for j in range(largura) ]

# cada numero só aparece uma vez
distinct_c   = [ Distinct([ X[i][j] for i in range(altura) for j in range(largura) ]) ]

# a soma de todas as linhas dá o valor no fim
rows_c   = [ And(sum(X[i])==somaLinhas[i]) for i in range(altura) ]

# soma de todas as colunas tem de dar o valor no fim
cols_c   = [ And(sum([ X[i][j] for i in range(altura) ])==somaColunas[j])
             for j in range(largura) ]

#todas as regras juntas
survo_c = cells_c + distinct_c + rows_c + cols_c

# Survo instance
instance = [ If(tup[i][j] == 0,
                  True,
                  X[i][j] == tup[i][j])
               for i in range(altura) for j in range(largura) ]
'''
Aplicar o solver as regras geradas
'''
s = Solver()
s.add(survo_c + instance)
if s.check() == sat:
    m = s.model()
    r = [ [ m.evaluate(X[i][j]) for j in range(largura) ]
          for i in range(altura) ]
    writeTofile(r,X,altura,largura,somaLinhas,somaColunas)
else:
    print("failed to solve")

print(instance)
