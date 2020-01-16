module clinica

open util/ordering[Time] as to 

----assinaturas---
sig Time {}

one abstract sig Clinica { 
 localizacao: some Filial
}

abstract sig Filial {
    servicos: set Servico
}

abstract sig Servico {
    profissional: some Profissional,
    ajudante: set Ajudante
}

sig Odontologia, Psicologia, Fisioterapia extends Servico {}

sig Profissional{
    pacienteEmAtendimento:  set Paciente -> Time,
    pacientesNaoAtendidos:  set Paciente -> Time,
    pacientesAtendidos: set  Paciente -> Time
}

one sig CampinaGrande, JoaoPessoa, Patos, SantaRita extends Filial {}

sig Ajudante{}

sig Paciente{}

----------------------------------- FATOS --------------------------------

fact filial{
    //Toda filial esta ligada a sua matriz
    all fil: Filial | some fil.~localizacao
    // Os servicos de Odontologia, Psicologia e Fisioterapia estao presentes em toda clinica
    all fil: Filial | one o: Odontologia | one p: Psicologia | one f: Fisioterapia |
    let ser = fil.servicos | o in ser and p in ser and f in ser
}

fact servico {
    // Todo serviço pertence a uma filial
    all s: Servico | some s.~servicos 
    // Todo serviço tem apenas um medico
    all s: Servico | one s.profissional
    // Os servicos de Odontologia, Psicologia e Fisioterapia não podem estar simultaneamente em outra clinica
    all o: Odontologia, fil: Filial | (o in fil.servicos => (all fil2: Filial - fil | o !in fil2.servicos))
    all p: Psicologia, fil: Filial | (p in fil.servicos => (all fil2: Filial - fil | p !in fil2.servicos))
    all f: Fisioterapia, fil: Filial | (f in fil.servicos => (all fil2: Filial - fil | f !in fil2.servicos))    
    -------- Quantidades de ajudante em cada serviço ----------
    // Odontologia = 1
    all o: Odontologia | one o.ajudante
    //Psicologia = 0
    all p: Psicologia | no p.ajudante
    // Fisioterapia = 1 a 3
    all f: Fisioterapia | #ajudantesDeFisioterapia[f] >= 1 && #ajudantesDeFisioterapia[f] <= 3
}

fact ajudante {
     // Todo ajudante esta em um servico
    all ajud: Ajudante | some ajud.~ajudante 
    //Todo ajudande não pode estar em outro serviço simultaneamente
    all ajud: Ajudante, ser: Servico | (ajud in ser.ajudante => (all ser2: Servico  - ser | ajud !in ser2.ajudante))
}

fact profissional {    
    //todo medico faz parte do grupo de medicos de algum serviço da clinica
    all prof: Profissional | some prof.~profissional
    // Todo medico atende até 5 pacientes
    all prof: Profissional, t: Time | #(getPacientes[prof, t]) <= 5
    //Todo medico  não pode estar em outro serviço simultaneamente
    all prof: Profissional , ser: Servico | (prof in ser.profissional => (all ser2: Servico  - ser | prof !in ser2.profissional))
}  


fact paciente {
    // Todo paciente esta ligado a um medico
    all p: Paciente, t: Time | one prof: Profissional | p in ( getPacientes[prof, t])
    // Todo paciente nao pode estar em outro medico simultaneamente
    all pac: Paciente , prof: Profissional, t: Time | (pac in getPacientes[prof, t] => (all prof2: Profissional  - prof | pac !in getPacientes[prof2, t]))
}

fact sistema {
    #Clinica= 1
    restricao 
}

----------------------------------- PREDICADOS --------------------------------

pred restricao {
        //Todo medico tem apenas um paciente em atendimento
    all t: Time, prof: Profissional | lone prof.pacienteEmAtendimento.t
    // o paciente que está em Não Atendido não pode estar Em Atendimento e Atendido
    all p: Paciente, t: Time,prof: Profissional | (p in prof.pacientesNaoAtendidos.t ) => 
    ((p not in prof.pacienteEmAtendimento.t) and (p not in prof.(pacientesAtendidos.t)))

    // o paciente que está Em Atendido não pode estar Não Atendido e Atendido
    all p: Paciente, t: Time,prof: Profissional | (p in prof.pacienteEmAtendimento.t ) => 
    ((p not in prof.pacientesNaoAtendidos.t) and (p not in prof.pacientesAtendidos.t))

    // o paciente que está em Atendido não pode estar Não Atendido e Em Atendido
    all p: Paciente, t: Time,prof: Profissional | (p in prof.pacientesAtendidos.t ) => 
    ((p not in prof.pacientesNaoAtendidos.t) and (p not in prof.pacienteEmAtendimento.t))
}


pred pacientesNaEsperaNaoMudam[prof: set Profissional, t, t': Time]{
	all prof1: prof | 
	(prof1.pacientesNaoAtendidos).t' = 	(prof1.pacientesNaoAtendidos).t
}

pred pacientesEmAtendimentoNaoMudam[pro: set Profissional, t, t': Time]{
all prof : pro |
	(prof.pacienteEmAtendimento).t' = 	(prof.pacienteEmAtendimento).t
}

pred pacientesAtendidosNaoMudam[pro: set Profissional, t, t': Time]{
all prof: pro |
	(prof.pacientesAtendidos).t' = 	(prof.pacientesAtendidos).t 
}

-------------------------------------------------------------------------------------------------------------

----------------------------------- FUNCOES --------------------------------
fun ajudantesDeFisioterapia[ser : Servico]: set Ajudante{
    ser.ajudante        
}

fun getPacientes[prof: Profissional, t: Time]: set Paciente{
    prof.pacienteEmAtendimento.t + prof.pacientesNaoAtendidos.t + prof.pacientesAtendidos.t
}

fun getPacienteEmAtendimento[prof: Profissional, t: Time]: set Paciente{
    prof.pacienteEmAtendimento.t 
}

----------------------------------- OPERAÇÕES TEMPORAIS --------------------------------

fact traces {
    init[first]
    all pre: Time-last | let pos = pre.next |
    some prof : Profissional, paciente: Paciente |
    addPaciente[prof, paciente, pre, pos] or
    atenderPaciente[prof, paciente, pre, pos] or
    terminarAtendimento[prof, paciente, pre, pos]

}

pred init[t: Time] {
    no (Profissional.pacientesAtendidos).t
    no (Profissional.pacienteEmAtendimento).t
}

pred addPaciente[prof: Profissional, p: Paciente,t, t': Time] {
	// se paciente não estiver alocado para nenhum profissional, ele é adicionado
	all prof2: Profissional | (p !in getPacientes[prof2, t]) => ((prof.pacientesNaoAtendidos).t' = (prof.pacientesNaoAtendidos).t + p)
    
	// verifica se as outras listas(de todos os profissionais) continuam as mesmas
	pacientesNaEsperaNaoMudam[Profissional - prof, t, t']
   pacientesEmAtendimentoNaoMudam[ Profissional, t, t']
   pacientesAtendidosNaoMudam[Profissional, t, t']
   
}  

pred terminarAtendimento[prof: Profissional, p: Paciente,t, t': Time]{
	//se paciente estiver EmAtendimento do profissinal, termina o atendimento
    p in prof.pacienteEmAtendimento.t => 
	prof.pacienteEmAtendimento.t' = prof.pacienteEmAtendimento.t - p    
	
	prof.pacientesAtendidos.t' = prof.pacientesAtendidos.t + p    
	
	//verifica se as outras listas(de todos os profissionais) continuam as mesmas
   pacientesNaEsperaNaoMudam[Profissional, t, t']
   pacientesEmAtendimentoNaoMudam[ Profissional - prof, t, t']
   pacientesAtendidosNaoMudam[Profissional- prof, t, t']
    

}

pred atenderPaciente[prof: Profissional, p: Paciente,t, t': Time]{   
	// se paciente estiver na lista NaoAtendidos de dado profissional (prof), e não estiver na lista de 
	//Atendidos do mesmo profissional, entede-se o paciente (p) 
	(p in prof.pacientesNaoAtendidos.t ) and (p !in prof.pacientesAtendidos.t)
   => prof.pacientesAtendidos.t' = prof.pacientesAtendidos.t + getPacienteEmAtendimento[prof,t]

	prof.pacienteEmAtendimento.t' =  prof.pacienteEmAtendimento.t + p
   	prof.pacientesNaoAtendidos.t' = prof.pacientesNaoAtendidos.t - p    

	//verifica se as outras listas(de todos os profissionais) continuam as mesmas
   	pacientesNaEsperaNaoMudam[Profissional - prof, t, t']
   	pacientesEmAtendimentoNaoMudam[Profissional - prof, t, t']
   	pacientesAtendidosNaoMudam[Profissional - prof, t, t']

}

------------------------------------ ASSERTS ------------------------------------
assert todoServicoTemApenasUmMedico{
    all prof:Profissional | prof in Servico.profissional
}

assert todaFilialPertenceAClinica{
    all f:Filial | f in Clinica.localizacao
}

assert todoServicoFisioterapiaTemApenasUmAjudante{
    all f: Fisioterapia | #ajudantesDeFisioterapia[f] >= 1 && #ajudantesDeFisioterapia[f] <= 3
}

assert todoPacienteEstaAlocadoParaUmMedico{
    all p: Paciente, t: Time | p in getPacientes[Profissional,t]
}


assert todoServicoOdontologiaTemApenasUmAjudante{
    all o: Odontologia | #o.ajudante = 1
}

assert  todoServicoPsicologiaNaoPossuiAjudante{
    all p: Psicologia | #p.ajudante = 0
}

assert  todoProfissionalSoAtendeUmPacientePorVez{
    all t: Time , p: Profissional | #p.pacienteEmAtendimento <= 1
}

assert  todoProfissionalAtendeAte5Pacientes{
    all p: Profissional | #(p.pacienteEmAtendimento + p.pacientesAtendidos + p.pacientesNaoAtendidos) <= 5
}




run init for 15    
check todoServicoTemApenasUmMedico for 15
check  todaFilialPertenceAClinica for 15
check todoServicoFisioterapiaTemApenasUmAjudante for 15
check todoPacienteEstaAlocadoParaUmMedico for 15
check  todoServicoOdontologiaTemApenasUmAjudante for 15
check todoServicoPsicologiaNaoPossuiAjudante for 15 
check todoProfissionalSoAtendeUmPacientePorVez for 15
check todoProfissionalAtendeAte5Pacientes for 15


