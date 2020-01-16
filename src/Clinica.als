module clinica/Clinica

open clinica/Cidade
open clinica/Servico

sig Clinica {
	localizacao: Cidade,
	servicos: set Servico
}
// dá erro na hora de executar
pred temServico[cli: Clinica, servico: Servico] {
	servico in cli
}


/* 
Uma clínica médica está localizada em quatro cidades da Paraíba: Campina Grande, Santa Rita, João Pessoa e Patos. 
Cada clínica oferece três serviços: Odontologia, Psicologia e Fisioterapia. 
Cada serviço deve ter um profissional da área (vamos chamar de médico). 
O serviço de odontologia precisa de apenas um ajudante, psicologia não precisa de nenhum e fisioterapia varia de um a três ajudantes.
 Cada médico pode atender até 5 pessoas por dia, mas não pode atender mais de uma pessoa ao mesmo tempo, logo o médico tem uma lista de pacientes a serem atendidos no dia.
*/
