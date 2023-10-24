/*
Três fazendeiros que compartilharam uma mula por um
tempo discutem quem é o verdadeiro dono do animal.
No entanto, pessoalmente nenhum deles quer se
responsabilizar pela mula. Os três fazem as seguintes
declarações, em que uma é verdadeira e outra é falsa.

A
1. A mula é de C. f
2. Não posso ser o dono. v 
B
1. C não é o dono. v
2. A mula é de A. f
C
1. A mula é minha. f  v
2. A segunda declaração de B é falsa v f
*/

sig Fazendeiro{}

one sig FA, FB, FC extends Fazendeiro{}

sig Dono in Fazendeiro{}

pred dono[f:Fazendeiro]{
    f in Dono
}

pred MULA_C{FC in Dono}
pred MULA_A{FA in Dono} 
pred MULA_NOT_A{FA not in Dono} 
pred MULA_NOT_C{FC not in Dono} 

fact "restricoes"{
    one f:Fazendeiro | dono[f]

    (#Dono=1)
    
    ((MULA_C and MULA_A) or (MULA_NOT_C and MULA_NOT_A)) 
    and 
    ((MULA_NOT_C and MULA_NOT_A) or (MULA_C and MULA_A))
    and
    ((MULA_C and MULA_A) or (MULA_NOT_C and MULA_NOT_A))

}

run{}