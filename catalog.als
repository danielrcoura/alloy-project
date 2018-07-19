module catalogo

------------------- SIGNATURE -------------------------

one sig Catalogo {
	moedas: set Moeda
}

sig Moeda {
	ano: one Ano,
	pais: one Pais,
	estado: one Estado,
	material: one Material,
	valor_compra: one Valor,
	valor_mercado: one Valor
}

sig Vendida, NaoVendida in Moeda {}

sig Ano {}
sig Pais {}
sig Valor {}

abstract sig Estado {}
lone sig Nova, Excelente, Bom, Ruim, Danificada extends Estado {}

abstract sig Material {}
lone sig Ouro, Prata, Bronze, Cobre, AcoInoxidavel, Outros extends Material {}

----------------------- FACTS --------------------------

-- A moeda deve ser vendida ou não
fact MoedaVendidaOuNaoVendida {
	no Vendida & NaoVendida
	Moeda = Vendida + NaoVendida
}

-- Cada moeda deve estar associada ao catálogo
fact TodaMoedaNoCatalogo {
	all m:Moeda | some m.~moedas
}

-- Cada país deve estar associado a pelo menos uma moeda
fact TodoPaisTemMoeda {
	all p:Pais | some p.~pais
}

-- Cada valor deve estar associado a uma moeda seja por compra ou mercado
fact TodoValorTemMoeda {
	all v:Valor | associadoComMoeda[v]
}

-- Cada ano deve estar associado a pelo menos uma moeda
fact TodoAnoTemMoeda {
	all a:Ano | some a.~ano
}

-- Cada estado deve estar associado a pelo menos uma moeda
fact TodoEstadoTemMoeda {
	all e:Estado | some e.~estado
}

-- Cada material deve estar associado a pelo menos uma moeda
fact TodoMaterialTemMoeda {
	all m:Material | some m.~material
}

----------------------- PREDS --------------------------

pred associadoComMoeda[v:Valor] {
	some v.~valor_compra || some v.~valor_mercado
}

----------------------- FUNCTIONS ------------------------

fun temMoedas[c:Catalogo]: set Moeda {
	c.moedas
}

----------------------- ASSERTS --------------------------

-- O catálogo pode ter várias ou nenhuma moeda
assert testeCatalogoComMoedas {
	all c:Catalogo | #temMoedas[c] >= 0
}

-- Toda moeda deve estar associada ao catálogo
assert testeMoedaPertenceACatalogo {
	all m:Moeda | #(m.~moedas) > 0
}

check testeCatalogoComMoedas
check testeMoedaPertenceACatalogo

pred show[]{}
run show
