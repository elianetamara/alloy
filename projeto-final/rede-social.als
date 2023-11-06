open util/boolean

one sig RedeSocial{
  usuarios: set Usuario,
  contas: set Perfil
}

sig Publicacao{
  autores: one Perfil
}

sig Perfil{
  status_perfil: one Bool,
  dono: one Usuario,
  publicacoes: set Publicacao,
}

sig Usuario{
  status_usuario: one Bool,
  amizades_ativas: set Usuario,
  amizades_inativas: set Usuario,
  // perfis: some Perfil
}

pred restringeAmizade[u: Usuario]{
  u not in u.amizades_ativas and u not in u.amizades_inativas
}

fact "amizades diferente de si mesmo"{
    all u: Usuario | restringeAmizade[u]
}

fact "usuarios e perfil dentro de RedeSocial"{
  all u:Usuario, p:Perfil, r:RedeSocial | u in r.usuarios and p in r.contas 
}

pred restringeUsuarioAtivo[u: Usuario]{
  u.status_usuario = boolean/True or u.status_usuario = boolean/False
}

fact "usuario ativo ou inativo"{
  all u: Usuario | restringeUsuarioAtivo[u]
}

pred restringePerfilAtivo[p: Perfil]{
  p.status_perfil = boolean/True or p.status_perfil = boolean/False
}

fact "perfil ativo ou inativo"{
  all p: Perfil | restringePerfilAtivo[p]
}

fact "usuarios inativos sem amizades"{
  all u1: Usuario | boolean/isFalse[u1.status_usuario] implies no u1.amizades_ativas
}

fact "usuarios inativos com perfis inativos"{
  all u: Usuario | u.status_usuario = boolean/False implies all p: Perfil | p.dono = u and p.status_perfil = boolean/False
}

fact "postagens relacionadas a perfis ativos"{
  all p1:Publicacao |  one p: Perfil | p1 in p.publicacoes and p.status_perfil = boolean/True
}

fact "usuario tem acesso a publicar texto em perfil de amigos"{
//usuário pode publicar conteúdo de texto em seu perfil ou nos perfis de seus amigos.
  //all u1:Usuario, u2:Usuario | u1 in u2.amizades_ativas implies u2.perfis.publicacoes in u1.perfis.publica 
}

fact "amizade nao pode ser ativa e inativa ao mesmo tempo"{
  all u1, u2: Usuario | u1 in u2.amizades_ativas implies u2 in u1.amizades_ativas
  all u1, u2: Usuario | u1 in u2.amizades_inativas implies u2 in u1.amizades_inativas
  all u1, u2: Usuario | u1 in u2.amizades_ativas implies u1 not in u2.amizades_inativas
}

run {} for 3 but exactly 3 Usuario

check usuariosInativosSemAmizades {
  all u: Usuario | u.status_usuario = boolean/False implies no u.amizades_ativas
}

check usuarioNaoAmigoDeSiMesmo {
  all u: Usuario | restringeAmizade[u]
}

check postagensEmPerfisAtivos {
  // all p1: Publicacao | p1 in p1.autores.publicacoes and p1.autores.status_perfil = boolean/True
}

check perfilAtivoOuInativo {
  all p: Perfil | restringePerfilAtivo[p]
}

check usuarioAtivoOuInativo {
  all u: Usuario | restringeUsuarioAtivo[u]
}

check usuariosComUmTipoAmizade {
  all u1, u2: Usuario | u1 in u2.amizades_ativas implies u2 in u1.amizades_ativas
  all u1, u2: Usuario | u1 in u2.amizades_inativas implies u2 in u1.amizades_inativas
  all u1, u2: Usuario | u1 in u2.amizades_ativas implies u1 not in u2.amizades_inativas
}

check perfilComUmDono {
  all p: Perfil | one p.dono
}

check usuarioPublicaEmPerfilAmigos {
  // all u1: Usuario, u2: Usuario | u1 in u2.amizades_ativas implies (all p: Perfil | p in u2.perfis implies p in u1.perfis)
}