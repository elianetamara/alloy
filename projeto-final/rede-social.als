sig Publicacao{
  usuario: lone Usuario
}

sig Perfil{
  dono: one Usuario,
  publicacoes: set Publicacao
}

sig Usuario{
  ativo: one Ativos,
  amizadesAtivas: set Usuario,
  amizadesInativas: set Usuario,
  perfis: some Perfil
}

sig Ativos, Inativos extends Usuario{}

fact "amizades diferente de si mesmo"{
    all u: Usuario | u not in u.^amizadesAtivas
    all u: Usuario | u not in u.^amizadesInativas
}


run{}