
sig Publicacao{
  usuario: lone Usuario
}

sig Usuario{
  ativo: lone Ativos,
  amizadesAtivas: set Usuario,
  amizadesInativas: set Usuario,
  publicacoes: set Publicacao
}

sig Ativos, Inativos extends Usuario{}


run{}