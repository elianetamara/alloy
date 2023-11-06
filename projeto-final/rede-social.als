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
  publicacoes: set Publicacao,
}

sig Usuario{
  ativo: one Bool,
  amizadesAtivas: set Usuario,
  amizadesInativas: set Usuario,
  perfis: some Perfil
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

pred restringeUsuarioAtivo[u: Usuario]{
  u.ativo = boolean/True or u.ativo = boolean/False
}

fact "usuario ativo ou inativo"{
  all u: Usuario | restringeUsuarioAtivo[u]
}

pred restringePerfilAtivo[p: Perfil]{
  p.ativo = boolean/True or p.ativo = boolean/False
}

fact "perfil ativo ou inativo"{
  all p: Perfil | restringePerfilAtivo[p]
}

fact "usuarios inativos sem amizades"{
  all u1: Usuario | boolean/isFalse[u1.ativo] implies no u1.amizadesAtivas
}

fact "usuarios inativos com perfis inativos"{
  all u: Usuario | u.ativo = boolean/False implies all p: Perfil | p.dono = u and p.ativo = boolean/False
}

fact "postagens relacionadas a perfis ativos"{
  all p1:Publicacao |  one p: Perfil | p1 in p.publicacoes and p.ativo = boolean/True
}

fact "usuario tem acesso a publicar texto em perfil de amigos"{
//usuário pode publicar conteúdo de texto em seu perfil ou nos perfis de seus amigos.
  //all u1:Usuario, u2:Usuario | u1 in u2.amizadesAtivas implies u2.perfis.publicacoes in u1.perfis.publica 
}

fact "perfil tem apenas um dono"{
  all p:Perfil | one u:Usuario | u in p.dono and p in u.perfis
}

/*
pred restringeTipoAmizade[u1: Usuario, u2: Usuario]{
  (u1 in u2.amizadesAtivas and u1 not in u2.amizadesInativas)
  and
  (u2 in u1.amizadesAtivas and u2 not in u1.amizadesInativas)
}

fact "usuarios tem amizade ativa ou inativa"{
  all u1: Usuario, u2: Usuario | restringeTipoAmizade[u1, u2] 
}
*/

run{} for 3

check usuariosInativosSemAmizades {
}

check usuarioNaoAmigoDeSiMesmo {
}

check postagensEmPerfisAtivos {
}

check perfilAtivoOuInativo {
}

check usuarioAtivoOuInativo {
}

check usuariosComUmTipoAmizade {
}

check perfilComUmDono {
}

check usuarioPublicaEmPerfilAmigos {
}