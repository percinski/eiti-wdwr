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

/******************* PARAMTERY METODY: WYMAGANY POZIOM ZYSKU ***********/
float minAvgProfit = ...; //wymagany poziom zysku

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
minimize giniRisk;
//maximize avgProfit;

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
  /******************OGRANICZENIE: WYMAGANY POZIOM ZYSKU ****************************/
  	avgProfit>=minAvgProfit;
  
}// Koniec ogranicznen  
 
main {
   var file = new IloOplOutputFile("result-minAvgProfit.txt");
   //var fileAP = new IloOplOutputFile("avgProfitScenario.txt");
   //var fileMR = new IloOplOutputFile("maxRiskScenario.txt");
   
   var mod  = thisOplModel;
   var def  = mod.modelDefinition;
   var data = mod.dataElements;
   var maxAvgProfit = 26553;
   var i = 1;
  
   file.writeln("i;minAvgProfit;avgProfit;giniRisk;m1_prod_P1;m1_prod_P2;m1_prod_P3;m1_prod_P4;m2_prod_P1;m2_prod_P2;m2_prod_P3;m2_prod_P4;m3_prod_P1;m3_prod_P2;m3_prod_P3;m3_prod_P4;m1_stock_P1;m1_stock_P2;m1_stock_P3;m1_stock_P4;m2_stock_P1;m2_stock_P2;m2_stock_P3;m2_stock_P4;m3_stock_P1;m3_stock_P2;m3_stock_P3;m3_stock_P4");
   
	 data.minAvgProfit = -600.0;
     
     	while (data.minAvgProfit <= maxAvgProfit) {
       		mod = new IloOplModel (def, cplex);
       		mod.addDataSource(data);
       		mod.generate();
       		cplex.tilim = 300;
       		cplex.solve();
       		file.writeln(i,";",data.minAvgProfit,";",mod.avgProfit,";",mod.giniRisk,";",mod.produce[1][1],";",mod.produce[1][2],";",mod.produce[1][3],";",mod.produce[1][4], ";",mod.produce[2][1],";",mod.produce[2][2],";",mod.produce[2][3],";",mod.produce[2][4],";",mod.produce[3][1],";",mod.produce[3][2], ";",mod.produce[3][3],";",mod.produce[3][4],";",mod.stock[1][1],";",mod.stock[1][2],";",mod.stock[1][3],";",mod.stock[1][4], ";",mod.stock[2][1],";",mod.stock[2][2],";",mod.stock[2][3],";",mod.stock[2][4],";",mod.stock[3][1],";",mod.stock[3][2], ";",mod.stock[3][3],";",mod.stock[3][4]);
       		writeln(i," minAvgProfit: ",data.minAvgProfit," avgProfit: ",mod.avgProfit,", giniRisk: ",mod.giniRisk);
       		mod.end();
       		data.minAvgProfit = data.minAvgProfit + 532.41;
       		i = i+1;
     	};
  
   
   file.close();
   //fileAP.close();
   //fileMR.close();
}