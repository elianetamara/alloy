/*
O computador ideal para Mariana tem que ser rápido, com boa
memória e compacto. Das quatro marcas que ela viu: Lenovo, Dell,
Apple, Acer, apenas uma delas tem as 3 características ao mesmo
tempo
Sabemos que:
1. Apenas 3 são rápidos, apenas 2 tem boa memória, apenas um é
compacto.
2. Todas quatro marcas possuem pelo menos uma das características
3. Lenovo e Dell têm a mesma capacidade de memória.
4. Dell e Apple são igualmente rápidos.
5. Apenas um entre Apple e Acer é considerado rápido.
*/

sig Computador {}

sig Rapido, BoaMemoria, Compacto in Computador{}

one sig APPLE, DELL, LENOVO, ACER extends Computador{}

pred ideal[c: Computador]{
    (c in Rapido) and (c in BoaMemoria) and (c in Compacto)
}

fact "restricoes"{
    one x: Computador | ideal[x]

    (#Rapido=3) and (#BoaMemoria=2) and (#Compacto=1)

    all c:Computador | (c in Rapido) or (c in BoaMemoria) or (c in Compacto)

    (LENOVO in BoaMemoria) <=> (DELL in BoaMemoria)
    
    (DELL in Rapido) <=> (APPLE in Rapido)

    ((APPLE in Rapido) and (ACER not in Rapido))
     or 
    ((APPLE not in Rapido) and (ACER in Rapido))

}

run{}