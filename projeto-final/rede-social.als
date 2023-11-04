open util/boolean

one sig RedeSocial{
  usuarios: set Usuario,
  perfis: set Perfil
}

sig Publicacao{
  usuario: lone Usuario
}

sig Perfil{
  ativo: Bool,
  dono: one Usuario,
  publicacoes: set Publicacao
}

sig Usuario{
  ativo: Bool,
  amizadesAtivas: set Usuario,
  amizadesInativas: set Usuario,
  perfis: some Perfil
}

fact "amizades diferente de si mesmo"{
    all u: Usuario | u not in u.^amizadesAtivas
    all u: Usuario | u not in u.^amizadesInativas
}

fact "usuarios inativos sem amizades"{
  //all u:Usuario | boolean/isFalse[u.ativo] implies u.amizadesAtivas
}

fact "usuarios inativos com perfis inativos"{
  all u:Usuario | boolean/isFalse[u.ativo] implies all p:Perfil | u in p.dono implies boolean/False in p.ativo
}

fact "usuario tem acesso a publicar texto em perfil de amigos"{}

/*
fact "usuario acessa hierarquia"{
    all u: Usuario, r:Recurso | r in u.acessa implies inferiores[r] in u.acessa  
}
*/


run{} for 2

/*
e um usuário está inativo, podemos considerar 
todos os seus perfis como inativos

usuários inativos não possuem amizades

Um usuário pode publicar conteúdo de texto 
em seu perfil ou nos perfis de seus amigos.

 as postagens devem estar associadas a usuários ativos
*/