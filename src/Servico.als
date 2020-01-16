module clinica/Servico

sig Servico {
	profissional: one Profissional
}

one sig Odontologia, Psicologia, Fisioterapia extends Servico {}
