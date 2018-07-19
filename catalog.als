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
	all m:Moeda | estaNoCatalogo[m]
}

-- Cada país deve estar associado a pelo menos uma moeda
fact TodoPaisTemMoeda {
	all p:Pais | associadoComMoeda[p]
}

-- Cada valor deve estar associado a uma moeda seja por compra ou mercado
fact TodoValorTemMoeda {
	all v:Valor | associadoComMoeda[v]
}

-- Cada ano deve estar associado a pelo menos uma moeda
fact TodoAnoTemMoeda {
	all a:Ano | associadoComMoeda[a]
}

-- Cada estado deve estar associado a pelo menos uma moeda
fact TodoEstadoTemMoeda {
	all e:Estado | associadoComMoeda[e]
}

-- Cada material deve estar associado a pelo menos uma moeda
fact TodoMaterialTemMoeda {
	all m:Material | associadoComMoeda[m]
}

----------------------- PREDS --------------------------

pred estaNoCatalogo[m:Moeda] {
	some moedasNoCatalogo[m]
}

pred associadoComMoeda[p:Pais] {
	some paisesDasMoedas[p]
}

pred associadoComMoeda[v:Valor] {
	some valoresDeCompraDasMoedas[v] || some valoresDeMercadoDasMoedas[v]
}

pred associadoComMoeda[a:Ano] {
	some anosDasMoedas[a]
}

pred associadoComMoeda[e:Estado] {
	some estadosDasMoedas[e]
}

pred associadoComMoeda[m:Material] {
	some materiaisDasMoedas[m]
}

----------------------- FUNCTIONS ------------------------

fun moedasNoCatalogo[m:Moeda]: set Catalogo {
	moedas.m
}

fun paisesDasMoedas[p:Pais]: set Moeda {
	pais.p
}

fun valoresDeCompraDasMoedas[v:Valor]: set Moeda {
	valor_compra.v
}

fun valoresDeMercadoDasMoedas[v:Valor]: set Moeda {
	valor_mercado.v
}

fun anosDasMoedas[a:Ano]: set Moeda {
	ano.a
}

fun estadosDasMoedas[e:Estado]: set Moeda {
	estado.e
}

fun materiaisDasMoedas[m:Material]: set Moeda {
	material.m
}

fun temMoedas[c:Catalogo]: set Moeda {
	c.moedas
}


----------------------- ASSERTS --------------------------

-- O catálogo pode ter várias moedas
assert testeCatalogoComMoedas {
	all c:Catalogo | #temMoedas[c] >= 0
}

-- Toda moeda deve estar associada ao catálogo
assert testeMoedaPertenceACatalogo {
	all m:Moeda | #(m.~moedas) > 0
}

-- Se existe um material, então deve estar associado a uma moeda
assert testeMaterialPertenceAMoeda {
	all m:Material | #(m.~material) > 0 
}

check testeCatalogoComMoedas
check testeMoedaPertenceACatalogo
check testeMaterialPertenceAMoeda

pred show[]{}
run show
