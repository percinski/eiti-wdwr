/*********************************************
 * OPL 12.5.1.0 Model
 * Author: mateu
 * Creation Date: May 24, 2017 at 10:08:31 PM
 *********************************************/
 
 /***********PARAMETRY************************/
 //Paramatry zostaladniej opisane w pliku .dat oraz raporcie
 
// Parametry liczbowe
int nMachType = ...;
int nMonth = ...;
int nProdType = ...;

int nHours = ...;
int nScenarios = ...;

// Utworzenie wektorow indeksujacych
{int} machines = asSet(1..nMachType);
{int} months = asSet(1..nMonth);
{int} products = asSet(1..nProdType);
{int} scenarios = asSet(1..nScenarios);

//Parametry produkcji i sprzedazy
int machineCount[machines] = ...;
float prodTime[machines][products] = ...;
int maxInMonth[months][products] = ...;

//Parametry magazynowania
int storageMax[products] = ...;
int storageCost = ...;
int storageStart[products] = ...;

//Parametry do generowania scenariusze (nieuzywane w modelu CPLEX)
int mu[products] = ...;
int sigma[products][products] = ...;

//Macierz scenariuszy dochodow ze sprzedazy: typ produkty (kolumna) - scenariusz (wiersz)
float sellProfit[scenarios][products] = ...;

/*********** ZMIENNE DECYZYJNE ********************************************/
dvar int produce[months][products]; 	// Liczba wyprodukowanych
dvar int sell[months][products];		// Liczba sprzedanych
dvar int stock[months][products];		// Liczba w magazynie

// Czas wykorzystany na danym typie maszyna na dany typ produktu
dvar float workTime[months][machines][products];

// Zmienna binarna - czy sprzedaz danego typu produktu przekaroczyla 80 procent pojemnosci rynku
dvar boolean if80prec[months][products];

// Zmienna - ile pieniedzy nalezy odjac od dochodow z poszczegolnych produkow
// w poszczegolnych miesiacach ze wzgledu na przekroczenie 80% pojmnosci rynku
dvar float lowerProfit[scenarios][months][products];

/************ KRYTERIA OCENY *********************************************/
// ZYSK policzony dla poszczegolnych scenariuszy
dexpr float profit[i in scenarios] = sum(m in months, p in products) 
(sell[m][p]*sellProfit[i][p]-lowerProfit[i][m][p]- stock[m][p]*storageCost);

// wartosc oczekiwana zysku policzona jako srednia
dexpr float avgProfit = sum(i in scenarios)(profit[i])/nScenarios;

// RYZYKO zdefiniowane srednia roznica Giniego
dexpr float giniRisk = sum (t1 in scenarios, t2 in scenarios ) (
			0.5 * abs(profit[t1] - profit[t2]) * 1/nScenarios * 1/nScenarios
		);

// funkcja celu
//minimize giniRisk;
maximize avgProfit;

// ************** OGRANICZENIA ******************************************/
subject to {
  // Zmienne decyzyjne nie mniejsze niz zero
  forall(i in scenarios, m in months, mc in machines, p in products) {
    workTime[m][mc][p] >= 0;
    produce[m][p] >= 0;
    sell[m][p] >= 0;
    stock[m][p] >= 0;
    lowerProfit[i][m][p] >= 0;
  }    
  // Ogranicznie czasu produkcji maszyn w miesiacu
	forall(m in months, mc in machines) {
	  sum(p in products) (workTime[m][mc][p]) <= (machineCount[mc]*nHours);
  }
  // Ograniczenie definiujace wykorzystany czas pracy maszyn	
 	forall(m in months, p in products, mc in machines) {
 	  workTime[m][mc][p] == produce[m][p]*prodTime[mc][p];
  }
  // Ogranicznie maksymalnej pojemnosci rynku
 	forall(m in months, p in products) {
 	  sell[m][p] <= maxInMonth[m][p];
  }
  // Ogranicznie ustawiajace zmienna binarna po przekroczeniu 80 procent pojemnosci rynku
    forall(m in months, p in products) {
  	  sell[m][p] <= 0.8*maxInMonth[m][p] + 1000000 * if80prec[m][p];
  	  sell[m][p] >= 0.8*maxInMonth[m][p] * if80prec[m][p];
     }
  // Ograniczenia linearyzujace wplyw zmiennej binarnej na funkcje celu
    forall (i in scenarios,m in months, p in products) {
        lowerProfit[i][m][p] <= 1000000 * if80prec[m][p];
        lowerProfit[i][m][p] <= 0.2 * sell[m][p]*sellProfit[i][p];
        0.2 * sell[m][p]*sellProfit[i][p] - lowerProfit[i][m][p] + 1000000 * if80prec[m][p] <= 1000000;
    }        
  // Ograniczenie sprzedazy oraz definicja ilosci towaru pozostajacej w magazynie
  	forall(m in months, p in products) {
  	  if(m == 1) { //pierwszy miesiac
  	   sell[m][p] <= produce[m][p]+storageStart[p];
  	   stock[m][p]==(produce[m][p] + storageStart[p])-sell[m][p];
     }else {	// kolejne miesiace 
       sell[m][p] <= produce[m][p] + stock[m-1][p];
       stock[m][p]==(produce[m][p] + stock[m-1][p])-sell[m][p];
     }
  }
  // Ogranicznie maksymalnej ilosci magazynowanych produktow oraz 
  // wymaganej ilosc pozostalej w magazynie na na koniec symulacji
  	forall(m in months, p in products) {
  	  stock[m][p] <= storageMax[p];
  	  if(m == 3) {
  	  	stock[m][p] >= 50;
    }  	  	
   }
} 
execute {
 	cplex.tilim = 600;
	writeln("avgProfit: ",avgProfit,", giniRisk: ",giniRisk);
}