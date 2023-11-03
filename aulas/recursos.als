sig Local{
    recursos: set Recurso,
    usuarios: set Usuario 
}

sig Recurso{
    superior: lone Recurso
}

sig Usuario{
    acessa: set Recurso
}

fact "usuario nao compartilhado"{
    all u: Usuario | one l: Local | u in l.usuarios
}

fact "recurso nao compartilhado"{
    all r: Recurso | one l: Local | r in l.recursos
}

assert recursoNaoCompartilhado{
    !(some r: Recurso | #(recursos.r) > 1) 
}

check recursoNaoCompartilhado

fact "superior diferente de si mesmo"{
    all r: Recurso | r not in r.^superior
}

fun inferiores[r: Recurso]: set Recurso{
    {r1: Recurso | r in r1.^superior}
}

fact "usuario acessa hierarquia"{
    all u: Usuario, r:Recurso | r in u.acessa implies inferiores[r] in u.acessa  
}

run{} for 5 but exactly 2 Local

/*
some: pelo menos um
one: exatamente um
lone: 0 ou 1
set: conjunto
for 5: conjuntos no maximo com 5 objetos
*/