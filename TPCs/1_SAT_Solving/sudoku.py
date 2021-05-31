vars=[]
for linha in range(1,5):
    for coluna in range(1,5):
        for numero in range(1,5):
            vars.append('x' + str(linha) + str(coluna) + str(numero))

dictionary = {}
i = 1
for elem in vars:
    dictionary[elem] = i
    i+=1

## i = linha, j = coluna, i sempre menor que j
def getDictValue(coluna,linha,numero):
    cell = 'x' + str(linha) + str(coluna) + str(numero)
    return dictionary[cell]

def toFile():
    file = open("sudoku.cnf","w")
    file.write("p cnf 64 400\n")
    for col in range(1,5):
        for linha in range(1,5):
            for num in range(1,5):
                file.write(str(getDictValue(col,linha,num))+' ')
            file.write("0\n")

            for j in range(1,5):
                for ii in range(1,j):
                    num1 = getDictValue(col,linha,j)
                    num2 = getDictValue(col,linha,ii)
                    #print('-' + str(num2)+' -'+str(num1)+' 0')
                    file.write('-' + str(num2)+' -'+str(num1)+' 0\n')

    for numn in range(1,5):
        #EXCLUSIVIDADE DE SUB-MATRIZES
        file.write('-' + str(getDictValue(1,1,numn))+' -'+str(getDictValue(2,1,numn))+' 0\n')
        file.write('-' + str(getDictValue(1,1,numn))+' -'+str(getDictValue(2,2,numn))+' 0\n')
        file.write('-' + str(getDictValue(1,1,numn))+' -'+str(getDictValue(1,2,numn))+' 0\n')
        file.write('-' + str(getDictValue(2,1,numn))+' -'+str(getDictValue(2,2,numn))+' 0\n')
        file.write('-' + str(getDictValue(2,1,numn))+' -'+str(getDictValue(1,2,numn))+' 0\n')
        file.write('-' + str(getDictValue(1,2,numn))+' -'+str(getDictValue(2,2,numn))+' 0\n')

        file.write('-' + str(getDictValue(3,1,numn))+' -'+str(getDictValue(4,1,numn))+' 0\n')
        file.write('-' + str(getDictValue(3,1,numn))+' -'+str(getDictValue(4,2,numn))+' 0\n')
        file.write('-' + str(getDictValue(3,1,numn))+' -'+str(getDictValue(3,2,numn))+' 0\n')
        file.write('-' + str(getDictValue(4,1,numn))+' -'+str(getDictValue(4,2,numn))+' 0\n')
        file.write('-' + str(getDictValue(4,1,numn))+' -'+str(getDictValue(3,2,numn))+' 0\n')
        file.write('-' + str(getDictValue(3,2,numn))+' -'+str(getDictValue(4,2,numn))+' 0\n')

        file.write('-' + str(getDictValue(1,3,numn))+' -'+str(getDictValue(2,3,numn))+' 0\n')
        file.write('-' + str(getDictValue(1,3,numn))+' -'+str(getDictValue(2,4,numn))+' 0\n')
        file.write('-' + str(getDictValue(1,3,numn))+' -'+str(getDictValue(1,4,numn))+' 0\n')
        file.write('-' + str(getDictValue(2,3,numn))+' -'+str(getDictValue(2,4,numn))+' 0\n')
        file.write('-' + str(getDictValue(2,3,numn))+' -'+str(getDictValue(1,4,numn))+' 0\n')
        file.write('-' + str(getDictValue(1,4,numn))+' -'+str(getDictValue(2,4,numn))+' 0\n')

        file.write('-' + str(getDictValue(3,3,numn))+' -'+str(getDictValue(4,3,numn))+' 0\n')
        file.write('-' + str(getDictValue(3,3,numn))+' -'+str(getDictValue(4,4,numn))+' 0\n')
        file.write('-' + str(getDictValue(3,3,numn))+' -'+str(getDictValue(3,4,numn))+' 0\n')
        file.write('-' + str(getDictValue(4,3,numn))+' -'+str(getDictValue(4,4,numn))+' 0\n')
        file.write('-' + str(getDictValue(4,3,numn))+' -'+str(getDictValue(3,4,numn))+' 0\n')
        file.write('-' + str(getDictValue(3,4,numn))+' -'+str(getDictValue(4,4,numn))+' 0\n')

        for nm in range(1,5):
        #EXCLUSIVIDADE DE LINHAS
            file.write('-' + str(getDictValue(1,nm,numn))+' -'+str(getDictValue(2,nm,numn))+' 0\n')
            file.write('-' + str(getDictValue(1,nm,numn))+' -'+str(getDictValue(3,nm,numn))+' 0\n')
            file.write('-' + str(getDictValue(1,nm,numn))+' -'+str(getDictValue(4,nm,numn))+' 0\n')
            file.write('-' + str(getDictValue(2,nm,numn))+' -'+str(getDictValue(3,nm,numn))+' 0\n')
            file.write('-' + str(getDictValue(2,nm,numn))+' -'+str(getDictValue(4,nm,numn))+' 0\n')
            file.write('-' + str(getDictValue(3,nm,numn))+' -'+str(getDictValue(4,nm,numn))+' 0\n')
        #EXCLUSIVIDADE DE COLUNAS
            file.write('-' + str(getDictValue(nm,1,numn))+' -'+str(getDictValue(nm,2,numn))+' 0\n')
            file.write('-' + str(getDictValue(nm,1,numn))+' -'+str(getDictValue(nm,3,numn))+' 0\n')
            file.write('-' + str(getDictValue(nm,1,numn))+' -'+str(getDictValue(nm,4,numn))+' 0\n')
            file.write('-' + str(getDictValue(nm,2,numn))+' -'+str(getDictValue(nm,3,numn))+' 0\n')
            file.write('-' + str(getDictValue(nm,2,numn))+' -'+str(getDictValue(nm,4,numn))+' 0\n')
            file.write('-' + str(getDictValue(nm,3,numn))+' -'+str(getDictValue(nm,4,numn))+' 0\n')



print("---------- BEGIN ----------")
print(dictionary)
toFile()
print("----------- END -----------")
