## Programmazione 2 - AA 2018-2019
### Secondo progetto

Il progetto ha l’obiettivo di applicare a casi specifici i concetti e le tecniche di implementazione dei linguaggi 
di programmazione esaminate durante la seconda parte del corso. Il progetto  consiste nella progettazione 
e realizzazione di un interprete per un semplice linguaggio di programmazione.
Si consideri un’estensione del linguaggio didattico funzionale presentato a lezione che permetta di 
manipolare come dati primitivi dizionari di elementi, ovvero una collezione di coppie (chiave, valore). 
Assumiamo che la chiave sia un identificatore.

1. [ ] Si definisca la sintassi concreta del linguaggio e la sintassi astratta tramite una opportuna definizione di tipo in OCaML.
2. [ ] Si definisca l'interprete OCaML del linguaggio funzionale assumendo la regola di scoping statico.
4. [ ] Si verifichi la correttezza dell'interprete progettando ed eseguendo una quantità di casi di test sufficiente a testare tutti gli operatori aggiuntivi.

Opzionale
1. [ ] Estendere il linguaggio con un nuovo operatore rt_eval(exp) che prende in ingresso una espressione e restituisce il valore ottenuto eseguendo exp con la regola di scoping dinamico.
2. [ ] Si verifichi la correttenza dell'interprete progettando ed eseguendo una quantità di casi di test sufficiente a testare tutti gli operatori aggiuntivi.
