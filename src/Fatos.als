module clinica/Fatos

open clinica/Clinica

fact NumServicosClinica {
	// Cada clínica oferece três serviços.
	all cli: Clinica | #cli.servicos = 3 
}

fact TiposServicos {
	// Os servicos de Odontologia, Psicologia e Fisioterapia estao presentes em toda clinica
	all cli: Clinica | one o: Odontologia | one p: Psicologia | one f: Fisioterapia |
		let ser = cli.servicos | o in ser and p in ser and f in ser
}

fact LocalizacaoClinicas {} // A definir


pred show[]{}
run show for 5
