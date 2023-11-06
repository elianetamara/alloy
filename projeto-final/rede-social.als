open util/boolean

one sig RedeSocial{
  usuarios: set Usuario,
  contas: set Perfil
}

sig Publicacao{
  autores: set Perfil
}

sig Perfil{
  ativo: one Bool,
  dono: one Usuario,
  publicacoes: set Publicacao
}

sig Usuario{
  ativo: one Bool,
  amizadesAtivas: set Usuario,
  amizadesInativas: set Usuario,
  perfis: some Perfil,
  publica: set Publicacao
}

pred restringeAmizade[u: Usuario]{
  u not in u.^amizadesAtivas and u not in u.^amizadesInativas
}

fact "amizades diferente de si mesmo"{
    all u: Usuario | restringeAmizade[u]
}

fact "usuarios e perfil dentro de RedeSocial"{
  all u:Usuario, p:Perfil, r:RedeSocial | u in r.usuarios and p in r.contas 
}

// usuários inativos não possuem amizades
pred semAmizades[u1:Usuario, u2:Usuario]{
  (!(u2 in u1.amizadesAtivas) and !(u1 in u2.amizadesAtivas))
}

fact "usuarios inativos sem amizades"{
  all u1: Usuario | boolean/isFalse[u1.ativo] implies some u2: Usuario | semAmizades[u1, u2]
}

//se um usuário está inativo, podemos considerar todos os seus perfis como inativos
fact "usuarios inativos com perfis inativos"{
  // dando errado
  all u:Usuario | boolean/isFalse[u.ativo] 
  <=> 
  all p:Perfil | u in p.dono implies boolean/False in p.ativo
}

// postagens devem estar associadas a perfis ativos
fact "postagens relacionadas a perfis ativos"{
  all p:Perfil, p1:Publicacao | p in p1.autores implies boolean/True in p.ativo 
}

//usuário pode publicar conteúdo de texto em seu perfil ou nos perfis de seus amigos.
fact "usuario tem acesso a publicar texto em perfil de amigos"{
//se p1 e p2 estao em autores de publicacao, p1 e p2 sao amigos ativos
  all u1:Usuario, u2:Usuario | u1 in u2.amizadesAtivas implies u2.perfis.publicacoes in u1.publica 
}

// usuarios tem varios perfis, mas perfil tem um dono


run{} for 3