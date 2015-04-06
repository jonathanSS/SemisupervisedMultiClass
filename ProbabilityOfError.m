(* ::Package:: *)

BeginPackage["probabilityOfError`"]
\[NonBreakingSpace]\[NonBreakingSpace]
  (*l_K related functions - Section VI*)
  LKEQ::usage\[NonBreakingSpace]=\[NonBreakingSpace]"LKEQ[K_] calculates the l_K value for a problem with K equiprobable clases."; (*equip.*)
  LKEQPlot::usage\[NonBreakingSpace]=\[NonBreakingSpace]"LKEQPlot[max_] plots the l_K values for problems of 1..max equiprobable classes.";(*no equip.*)
  LKPriors::usage\[NonBreakingSpace]=\[NonBreakingSpace]"LKpriors[priors_,nRep_] use a Monte Carlo method with nRep repetitions to approximate l_k for a problem with Length[priors] non-equiprobable classes with priors given by the variable priors.";
  LKSampling::usage = "LKSampling[k_,samplesize_,nRep_,folder_] applies LKpriors over a population of size samplesize generate from a Dirichlet distributions with all alphas equal to 1.";
  L3Value::usage\[NonBreakingSpace]=\[NonBreakingSpace]"L3[n1_,n2_,n3_] calculates l_k for a 3-class problem with priors n1,n2 and n3.";
  L3Plot::usage\[NonBreakingSpace]=\[NonBreakingSpace]"L3Plot[] plots the variation of l_3 as presented in Figure 2b of the paper.";

  (*Functions related to the probability of error - Section VII and Section VIII*)
  ZeroEB::usage\[NonBreakingSpace]=\[NonBreakingSpace]"ZeroEB[K_,maxL_] calculates the probability of error for L={0..maxL} for a K class problem when there are no intersection between the components";
   (*eB > 0*)
\[NonBreakingSpace]\[NonBreakingSpace]MCPCSSL::usage\[NonBreakingSpace]=\[NonBreakingSpace]"MCPCSSL[K_,distance_,sigma_,maxL_, nRep_] use a Monte Carlo method with nRep repetitions to approximate the probability of error (l=0..maxL) of PCSSL asumming a mixture of K Gaussian, with distance between the means and sigma representing the variance.";
  MCPCSSLBiased::usage\[NonBreakingSpace]=\[NonBreakingSpace]"MCPCSSLBiased[K_,distance_,sigma_,maxL_, nRep_, bias_]. It works as MCPCSSL, but the means of the learnt model are moved by the factor bias.";
  MCVOTING::usage\[NonBreakingSpace]=\[NonBreakingSpace]"MCVOTING[K_,distance_,sigma_,maxL_, nRep_] use a Monte Carlo method with nRep repetitions to approximate the probability of error (l=0..maxL) of VOTING asumming a mixture of K Gaussian, with distance between the means and sigma representing the variance.";
  MCComparison::usage\[NonBreakingSpace]=\[NonBreakingSpace]"MCComparison[K_,distance_,sigma_,maxL_, nRep_] compares PCSSL and VOTING following the same procedure as the MCPCSSL and MCVOTING functions.";
  
(************************************
AUXILIARY FUNCTIONS
*************************************)
  
\[NonBreakingSpace]\[NonBreakingSpace]Begin["`Private`"]
g
	(*Hungarian algorithm (Kuhn,1955)*)
	Hungarian[costM_,Maximisation_]:= Module[{},
		Do[

			(*
			Transforming the maximisation problems into minisation ones
			*)
			If[Maximisation,CM0= Max[costM] -1*costM,CM0 = costM];
			Steps = {};
			step = 0;
			While[step < 7,
				Switch[step,

				0,
					AppendTo[Steps,0];
					(*
					Step 0: Rotate the matrix so that there are at least as many columns as rows.
					Go to Step 1.
					*)
					If[Length[CM[[1]]] <Length[CM], CM = Transpose[CM0],CM = CM0];
					n = Length[CM];
					m = Length[CM[[1]]];
					k = Min[n,m];
					step++,

				1,
					AppendTo[Steps,1];
					(*
					Step 1: For each row of the matrix, 
					find the smallest element and subtract it from every element in its row.
					Go to Step 2.
					*)
					auxCM = {};
					Do[auxR = CM[[row]];AppendTo[auxCM,auxR - Min[auxR]] ,{row,1,n}]; 
					CM = auxCM;
					step++,

				2,
					AppendTo[Steps,2];
					(*
					Step 2: Find a zero (Z) in the resulting matrix. 
					If there is no starred zero in its row or column, star Z. 
					Repeat for each element in the matrix. 
					Go to Step 3. 
					*)
					M =0* CM;
					Rcov = 0*CM[[1]];
					Ccov = 0*Transpose[CM][[1]];
					Do[
						aux = CM[[i]];
						Do[ 
							If[aux[[j]]==0 && Rcov[[i]] == 0 && Ccov[[j]] == 0,
								M[[i,j]] =1;
								Rcov[[i]] = 1;
								Ccov[[j]] = 1,
							Null]
						,{j,1,n}]
					,{i,1,m}];
					Do[Rcov[[i]] = 0,{i,1,n}];
					Do[Ccov[[j]] = 0,{j,1,m}];
					step++,

				3,
					AppendTo[Steps,3];
					(*
					Step 3: Cover each column containing a starred zero. 
					If K columns are covered, the starred zeros describe 
					a complete set of unique assigments. In this case, we are done. 
					If not, go to Step 4.
					*)
					Do[
						If[Count[M[[All,j]],1]>0, Ccov[[j]] = 1,Null],
						{j,1,m}];
					If[Count[Ccov,1] >= k, step=7, step=4],

				4,
					AppendTo[Steps,4];
					(*
					Step4: Find a non-covered zero and prime it.
					If there is no starred zero in the row containing this primed zero, go to Step 5.
					Otherwise, cover this row and uncover the column containing the starred zero.
					Continue in this manner until there are no uncovered zeros left. 
					Save the smallest uncovered value and go to Step 6.
					*)
					NotDone = True;
					r0= -1;
					c0= -1;
					While[NotDone,
						Zeros = {};
						Zeros = Position[CM,0];
						AuxZeros = {};
						Pos1 ={};
						Do[
							Pos1 = Zeros[[a]];
							If[CM[[Pos1[[1]],Pos1[[2]]]]==0 && Rcov[[Pos1[[1]]]] ==  0  && Ccov[[Pos1[[2]]]]== 0,
								AppendTo[AuxZeros,Zeros[[a]]],
							Null],
						{a,1,Length[Zeros]}];
						Zeros = AuxZeros;
						If[Length[Zeros]==0,
							step=6;
							Break[],
						Null];
						Do[
							Pos2 = {};
							Pos2= Zeros[[a]];
							M=ReplacePart[M,{Pos2[[1]],Pos2[[2]]}->2];
							If[Count[M[[Pos2[[1]],All]],1]> 0,
								c=0;
								star = 0;
								While[star==0,
									c++;
									If[M[[Pos2[[1]],c]]==1,star =c,Null]
								];
								Rcov[[Pos2[[1]]]] = 1;
								Ccov[[star]] =0,
							NotDone = False;
							step =5 ;
							r0 =Pos2[[1]]; 
							c0 =Pos2[[2]];
							Break[]]
						,{a,1,Length[Zeros]}]
					],

				5,
					AppendTo[Steps,5];
					(*
					Step5: Construct a series alternating primed and starred zeros.
					*)
					r1 = -1;
					c1 = -1;
					pathCount = 1;
					path = {{},{}};
					AppendTo[path[[1]] ,r0];
					AppendTo[path[[2]] ,c0];
					NotDone = True;
					While[NotDone,
						If[Count[M[[All,path[[2,pathCount]]]],1]> 0,
							star = 0;
							r=0;
							While[star==0,
								r++;
								If[M[[r,path[[2,pathCount]]]]==1,star =r,Null]
							];
							pathCount++;
							AppendTo[path[[1]],star];
							AppendTo[path[[2]],path[[2,pathCount-1]]],
						NotDone = False];
						If[NotDone,
							prime = 0;
							c=0;
							While[prime==0,
								c++;
								If[M[[path[[1,pathCount]],c]]==2,prime =c,Null]
							];
							pathCount++;
							AppendTo[path[[1]],path[[1,pathCount-1]]];
							AppendTo[path[[2]], prime],
						Null];
					];
					Do[Rcov[[i]] = 0,{i,1,n}];
					Do[Ccov[[j]] = 0,{j,1,m}];
					Do[replacement =1;
						If[M[[path[[1,p]],path[[2,p]]]] ==1,
							M=ReplacePart[M,{path[[1,p]],path[[2,p]]}->0],
						M=ReplacePart[M,{path[[1,p]],path[[2,p]]}->1]];
					,{p,1,pathCount}];
					Do[
						Do[
							If[M[[i,j]]==2, M = ReplacePart[M,{i,j} -> 0],Null]
						,{j,1,m}]
					,{i,1,n}];
					step = 3,

				6,
					AppendTo[Steps,6];
					(*
					Step6: Add the minimum non-zero value in the matrix to every element of each covered row 
					and substract it from every element of each uncovered column.
					Return to Step 4 without altering any stars, primes, or covered lines.
					*)
					min = Max[CM];
					Do[
						Do[ 
							If[min > CM[[i,j]] && Rcov[[i]] == 0 && Ccov[[j]] == 0,
								min = CM[[i,j]],
							Null]
						,{j,1,m}]
					,{i,1,n}];
					Do[
						Do[ 
							If[Rcov[[i]] == 1 ,
								CM[[i,j]]+= min,
							Null];
							If[Ccov[[j]] == 0,
								CM[[i,j]] -= min,
							Null]
						,{j,1,m}]
					,{i,1,n}];
					a=1;
					step = 4
				]
			]; 
			Return[M]
		,{1}]];

(*Functions using permutations*)
	Permutation2Index[permu_] := 
		Do[
			d= permu;
			n=Length[d];
			For[i=1,i<= n-1,i++,
				For[j=i+1,j<= n,j++,If[d[[j]]>d[[i]], d[[j]]-=1,Null]
				]
			];
			d-=1;
			sum = 1;
			For[s=1,s<=n,s++, sum+=Factorial[n-s]*d[[s]]];
			Return[sum],{1}];

	Index2Permutation[num_,size_] := 
		Do[
			index=num;
			permu={};
			Do[AppendTo[permu,0],{z,1,size}];
			index -=1;
			j=size-1;

			For[i=2,i<= size,i++,permu[[j]]=Mod[index,i];index=IntegerPart[index/i];j-- ];
			Do[
				Do[
					If[permu[[i]]>= permu[[j]],permu[[i]]+=1,Null]
				,{j,i-1,1,-1}]
			,{i,size,2,-1}];
			Return[permu+1]
		,{1}];

(*Auxiliary functions for the probability of error*)

	GenerateMeans[K_,distance_]:= Module[{},Do[
		means = {0};
		Do[AppendTo[means,means[[a-1]]+distance],{a,2,K}];
		Return[means];
	,{1}]];

	GenerateData[numK_,l_,means_,variance_, randomizer_] := Module[{},

		Ci = {};
		auxC = {};
		Do[AppendTo[Ci,auxC],{a,1,numK}];
		Do[

			class = RandomInteger[{1,numK}];
			normal=NormalDistribution[means[[class]],variance];AppendTo[Ci[[randomizer [[class]]]],Random[normal]]
		,{r2,1,l}];
		Return[Ci];
	];

	CreateVOTINGCostMatrix[Ci_,means_] := Module[{},Do[
		Rmax={};
		AuxR ={};
		Do[AppendTo[Rmax,AuxR],{a,1,Length[Ci]}];
		(*1*)
		AppendTo[Rmax[[1]],-Infinity];
		AppendTo[Rmax[[1]],(means[[1]] + means[[2]])/2];
		(*2..K*)
		Do[
			AppendTo[Rmax[[z]],(means[[z-1]] + means[[z]])/2];  
			AppendTo[Rmax[[z]],(means[[z]] + means[[z+1]])/2]
		,{z,2,Length[Ci]-1}];
		(*K*)
		AppendTo[Rmax[[Length[Ci]]],(means[[Length[Ci]-1]] + means[[Length[Ci]]])/2];
		AppendTo[Rmax[[Length[Ci]]],Infinity];

		(*Generation of the Confusion Matrix*)
		auxLS = {};
		Do[AppendTo[auxLS,{}],{LSi,1,Length[Ci]}];
		LabelledSubset = {};
		Do[AppendTo[LabelledSubset,auxLS],{LSj,1,Length[Ci]}];

		Do[(*CLASS LSi2:1-K*)
			Do[(*REGION LSj2:1-K*)
				LabelledSubset[[LSi2]][[LSj2]] = Select[Ci[[LSi2]],#>Rmax[[LSj2]][[1]]&& # <Rmax[[LSj2]][[2]]&]
			,{LSj2,1,Length[Ci]}]
		,{LSi2,1,Length[Ci]}];
		aux1 = {};
		Do[AppendTo[aux1,0],{VOTadd1,1,Length[Ci]}];
		CostMatrix = {};
		Do[AppendTo[CostMatrix,aux1],{VOTadd2,1,Length[Ci]}];
		Do[
			Do[
				CostMatrix[[row]][[column]] = Length[LabelledSubset[[row]][[column]]]
			,{column,1,Length[Ci]}]
		,{row,1,Length[Ci]}];
		Return[CostMatrix];

	,{1}]];

	CleanCM[CM_]:= Module[{},Do[
		minNoIndeterminate[C_]:=Block[{Indeterminate=+Infinity},Min[C]];
		aux = IntegerPart[CM*1000000];
		aux =aux +minNoIndeterminate[aux];
		Do[
			Do[
				If[aux[[r]][[c]]===Indeterminate,aux[[r]][[c]]=0,Null]
			,{c,1,Length[aux[[r]]]}]
		,{r,1,Length[aux]}];
		Return[aux],{1}]];

	CreatePCSSLCostMatrix[Ci_, means_,variance_]:=Module[{},Do[
		aux1 = {};
		Do[AppendTo[aux1,0],{PCSSLadd1,1,Length[Ci]}];
		CostMatrix = {};
		Do[AppendTo[CostMatrix,aux1],{PCSSLadd2,1,Length[Ci]}];
		Do[
			Do[ 
				If[ Length[Ci[[LSi]]]==0,
					CostMatrix[[LSi]][[LSj]] = Indeterminate,
					CostMatrix[[LSi]][[LSj]]= Sum[Log[PDF[NormalDistribution[means[[LSj]],variance],Ci[[LSi]][[a]]]],{a,1,Length[Ci[[LSi]]]}]];
			,{LSj,1,Length[Ci]}]
		,{LSi,1,Length[Ci]}];
		Return[CleanCM[CostMatrix]];
	,{1}]];

(*Calculating the probability of error of each classifier when the Bayes decision rule is applied*)
	
	Extrem1[c_,mu_,variance_] :=CDF[NormalDistribution[mu,variance],c];
	ExtremK[c_,mu_,variance_] :=1-CDF[NormalDistribution[mu,variance],c];
	MediumJ[c1_,c2_,mu_,variance_] :=CDF[NormalDistribution[mu,variance],c1]-CDF[NormalDistribution[mu,variance],c2];

	Stage3BDR[numC_,means_,variance_]:=Module[{},Do[
		BayesPi = {};
		Do[AppendTo[BayesPi,0],{a,1,numC!}];
		Do[
			auxP = Index2Permutation[b,numC];
			BayesPi[[b]]=(1/numC)*(1- Extrem1[(means[[1]] + means[[2]])/2,means[[auxP[[1]]]],variance] + 
					Sum[
						1 - MediumJ[(means[[j]] + means[[j+1]])/2,(means[[j]] + means[[j-1]])/2,means[[auxP[[j]]]],variance]
					,{j,2,numC-1}] + 
					1 - ExtremK[(means[[numC]] + means[[numC-1]])/2,means[[auxP[[numC]]]],variance]);
		,{b,1,Length[BayesPi]}];
		Return[BayesPi];
	,{1}]];

	Stage3BDRBiased[numC_,means_,variance_,bias_]:=Module[{},Do[
		BayesPi = {};
		Do[AppendTo[BayesPi,0],{a,1,numC!}];
		Do[
			auxP = Index2Permutation[b,numC];
			BayesPi[[b]]=(1/numC)*(1- Extrem1[(means[[1]] + means[[2]])/2+bias,means[[auxP[[1]]]],variance] + 
					Sum[
						1 - MediumJ[(means[[j]] + means[[j+1]])/2,(means[[j]] + means[[j-1]])/2+bias,means[[auxP[[j]]]],variance]
					,{j,2,numC-1}] + 
					1 - ExtremK[(means[[numC]] + means[[numC-1]])/2+bias,means[[auxP[[numC]]]],variance]);
		,{b,1,Length[BayesPi]}];
		Return[BayesPi];
	,{1}]];

(************************************
PC_SSL (Monte Carlo approx.)
*************************************)
\[NonBreakingSpace]\[NonBreakingSpace]
	MCPCSSL[K_,distance_,sigma_,maxL_, nRep_]\[NonBreakingSpace]:=\[NonBreakingSpace]Module[{},
		Do[

			(*Model*)
			means = GenerateMeans[K,distance];
			(*Error*)
			errorL = {};
			errorEB = {};
			(*Calculating errors of stage 3*)
			BayesPi=Stage3BDR[K,means,sigma];
			(*Classifiers*)
			clasifP = {};
			Do[AppendTo[clasifP,a],{a,1,K}];
			
			(*Printing1*)
			Print[Style["CHARACTERISTICS OF THE PROBLEM",Bold]];
			Print["- ",K," classes and mixture components which follow Gaussian distributions N(\[Mu],\[Sigma])."];
			Print["- ",Subscript["e","B"],": ",  N[BayesPi[[1]],5]," (Bayes error)."];
			Print["- The distance between the means of two adjacent components is ",distance,"."];
			Print["- \[Sigma] is equal to ", sigma,"." ];
			Print["- P(l,",Infinity,") for l={0,...",maxL "} is approximated by means of a Monte Carlo method (",nRep, "rep.)."];
			Print["- The possible correspondences \[Pi] between components and clases are:", Permutations[clasifP]];
			Print[Style["PROBABILITY OF ERROR[PCSSL]",Bold],"   P(l,",Infinity,")=", Style["\[CapitalSigma]",FontSize-> 36]," P(",Subscript["\[CapitalPi]","l"],"=\[Pi]) P(errBDR|\[Pi])"];
			Print[Style["Probability of error given a correspondence \[Pi]",Blue]];
			Print["P(errBDR|\[Pi]): ", N[BayesPi,5]];
			Print[Style["Probability of a correspondence \[Pi] with l labelled examples",Blue]];

			Do[(*l:0-maxL*)
				error = 0;
				probPermutation= {};
				Do[AppendTo[probPermutation,0],{a,1,K!}];

				Do[(*r1:1-nRep*)
					classifier = 0;
					If[l==0,
					(*l==0*)
						classifier= RandomInteger[{1,K!}]
					(*FIN l==0*),
					(*l>0*)
						randomizer = Index2Permutation[RandomInteger[{1,K!}],K];
						Ci = GenerateData[K,l,means,sigma, randomizer];
						(*PC-SSL - Linear Assignment Problem*)
						PCCM =CreatePCSSLCostMatrix[Ci, means,sigma];
						classifier = Permutation2Index[Permute[Position[Hungarian[PCCM,True],1][[All,2]],InversePermutation[randomizer]]]
					(*FIN l>0*)
					];(*Fi*)

					probPermutation[[classifier]] ++; 
					error += BayesPi[[classifier]];
				,{r1,1,nRep}];
				probPermutation /=nRep;
				error /= nRep;
				AppendTo[errorL,error];
				AppendTo[errorEB,N[BayesPi[[1]],5]]
				(*Printing2*)
				Print["P(",Subscript["\[CapitalPi]",l],"=\[Pi]): ", N[probPermutation,5]];
			,{l,0,maxL}];

			(*Printing3*)
			Print[Style["Probability of error",Blue]];
			Print["P(l,",Infinity,"):", N[errorL,5]];
			Print[Style["Illustration of the variation of the probability of error",Blue]];
			Print[ListPlot[{N[errorL],N[errorEB]},Joined->True,PlotLegends->{"PCSSL","Bayes Error"}, PlotRange -> {0,1},DataRange->{0,maxL},PlotStyle-> {{Thick,Blue},{Thick,Black}}]];
		,{1}]
	];

(************************************
PC_SSL biased (Monte Carlo approx.) u < Infinity 
*************************************)
\[NonBreakingSpace]\[NonBreakingSpace]
	MCPCSSLBiased[K_,distance_,sigma_,maxL_, nRep_,bias_]\[NonBreakingSpace]:=\[NonBreakingSpace]Module[{},
		Do[

			(*Model*)
			means = GenerateMeans[K,distance];
			(*Error*)
			errorL = {};
			errorEB = {};
			(*Calculating errors of stage 3*)
			BayesPiBiased=Stage3BDRBiased[K,means,sigma,bias];
			BayesPiReal=Stage3BDR[K,means,sigma];
			(*Classifiers*)
			clasifP = {};
			Do[AppendTo[clasifP,a],{a,1,K}];
			
			(*Printing1*)
			Print[Style["CHARACTERISTICS OF THE PROBLEM",Bold]];
			Print["- The CORRECT MODEL ASSUMPTION is NOT met. There is a bias of ",bias, " between the means of the generative and the learnt model."];
			Print["- ",K," classes and mixture components which follow Gaussian distributions N(\[Mu],\[Sigma])."];
			Print["- ",Subscript["e","B"],": ",  N[BayesPiReal[[1]],5]," (Bayes error)."];
			Print["- The distance between the means of two adjacent components is ",distance,"."];
			Print["- \[Sigma] is equal to ", sigma,"." ];
			Print["- P(l,",Infinity,") for l={0,...",maxL "} is approximated by means of a Monte Carlo method (",nRep, "rep.)."];
			Print["- The possible correspondences \[Pi] between components and clases are:", Permutations[clasifP]];
			Print[Style["PROBABILITY OF ERROR[PCSSL]",Bold],"   P(l,",Infinity,")=", Style["\[CapitalSigma]",FontSize-> 36]," P(",Subscript["\[CapitalPi]","l"],"=\[Pi]) P(errBDR|\[Pi])"];
			Print[Style["Probability of error given a correspondence \[Pi]",Purple]];
			Print["P(errBDR|\[Pi]): ", N[BayesPiReal,5]];
			Print[Style["Probability of a correspondence \[Pi] with l labelled examples",Purple]];

			Do[(*l:0-maxL*)
				error = 0;
				probPermutation= {};
				Do[AppendTo[probPermutation,0],{a,1,K!}];

				Do[(*r1:1-nRep*)
					classifier = 0;
					If[l==0,
					(*l==0*)
						classifier= RandomInteger[{1,K!}]
					(*FIN l==0*),
					(*l>0*)
						randomizer = Index2Permutation[RandomInteger[{1,K!}],K];
						Ci = GenerateData[K,l,means,sigma, randomizer];
						(*PC-SSL - Linear Assignment Problem*)
						PCCM =CreatePCSSLCostMatrix[Ci, means,sigma];
						classifier = Permutation2Index[Permute[Position[Hungarian[PCCM,True],1][[All,2]],InversePermutation[randomizer]]]
					(*FIN l>0*)
					];(*Fi*)

					probPermutation[[classifier]] ++; 
					error += BayesPiBiased[[classifier]];
				,{r1,1,nRep}];
				probPermutation /=nRep;
				error /= nRep;
				AppendTo[errorL,error];
				AppendTo[errorEB,N[BayesPiReal[[1]],5]]
				(*Printing2*)
				Print["P(",Subscript["\[CapitalPi]",l],"=\[Pi]): ", N[probPermutation,5]];
			,{l,0,maxL}];

			(*Printing3*)
			Print[Style["Probability of error",Purple]];
			Print["P(l,",Infinity,"):", N[errorL,5]];
			Print[Style["Illustration of the variation of the probability of error",Purple]];
			Print[ListPlot[{N[errorL],N[errorEB]},Joined->True,PlotLegends->{"Biased PCSSL","Bayes Error"}, PlotRange -> {0,1},DataRange->{0,maxL},PlotStyle-> {{Thick,Purple},{Thick,Black}}]];
		,{1}]
	];

(************************************
VOTING (Monte Carlo approx.)
*************************************)

	MCVOTING[K_,distance_,sigma_,maxL_, nRep_]\[NonBreakingSpace]:=\[NonBreakingSpace]Module[{},
		Do[

			(*Model*)
			means = GenerateMeans[K,distance];
			(*Error*)
			errorL = {};
			errorEB = {};
			(*Calculating errors of stage 3*)
			BayesPi=Stage3BDR[K,means,sigma];
			(*Classifiers*)
			clasifP = {};
			Do[AppendTo[clasifP,a],{a,1,K}];

			(*Printing1*)
			Print[Style["CHARACTERISTICS OF THE PROBLEM",Bold]];
			Print["- ",K," classes and mixture components which follow Gaussian distributions N(\[Mu],\[Sigma])."];
			Print["- ",Subscript["e","B"],": ",  N[BayesPi[[1]],5]," (Bayes error)."];
			Print["- The distance between the means of two adjacent components is ",distance,"."];
			Print["- \[Sigma] is equal to ", sigma,"." ];
			Print["- Pv(l,",Infinity,") for l={0,...",maxL "} is approximated by means of a Monte Carlo method (",nRep, "rep.)."];
			Print["- The possible correspondences \[Pi] between components and clases are:", Permutations[clasifP]];
			Print[Style["PROBABILITY OF ERROR[VOTING]",Bold],"   Pv(l,",Infinity,")=", Style["\[CapitalSigma]",FontSize-> 36]," P(",Subscript["\[CapitalSigma]","l"],"=\[Pi]) P(errBDR|\[Pi])"];
			Print[Style["Probability of error given a correspondence \[Pi]",Red]];
			Print["P(errBDR|\[Pi]): ", N[BayesPi,5]];
			Print[Style["Probability of a correspondence \[Pi] with l labelled examples",Red]];
			
			
			Do[(*l:0-maxL*)
				error = 0;
				probPermutation= {};
				Do[AppendTo[probPermutation,0],{a,1,K!}];

				Do[(*r1:1-nRep*)
					classifier = 0;
					If[l==0,
					(*l==0*)
						classifier= RandomInteger[{1,K!}]
					(*FIN l==0*),
					(*l>0*)
						randomizer = Index2Permutation[RandomInteger[{1,K!}],K];
						Ci = GenerateData[K,l,means,sigma, randomizer];
						(*PC-SSL - Linear Assignment Problem*)
						VOTCM = CreateVOTINGCostMatrix[Ci,means];
						classifier = Permutation2Index[Permute[Position[Hungarian[VOTCM,True],1][[All,2]],InversePermutation[randomizer]]]
					(*FIN l>0*)
					];(*Fi*)

					probPermutation[[classifier]] ++; 
					error += BayesPi[[classifier]];
				,{r1,1,nRep}];
				probPermutation /=nRep;
				error /= nRep;
				AppendTo[errorL,error];
				AppendTo[errorEB,N[BayesPi[[1]],5]]
				(*Printing2*)
				Print["P(",Subscript["\[CapitalSigma]",l],"=\[Pi]): ", N[probPermutation,5]];
			,{l,0,maxL}];


			Print[Style["Probability of error",Red]];
			Print["Pv(l,",Infinity,"):", N[errorL,5]];
			Print[Style["Illustration of the variation of the probability of error",Red]];
			Print[ListPlot[{N[errorL],N[errorEB]},Joined->True,PlotLegends->{"VOTING","Bayes Error"}, PlotRange -> {0,1},DataRange->{0,maxL},PlotStyle-> {{Thick,Red},{Thick,Black}}]];
		,{1}]];

(************************************
COMPARISON PCSSL-VOT (Monte Carlo)
*************************************)
	MCComparison[K_,distance_,sigma_,maxL_, nRep_]\[NonBreakingSpace]:=\[NonBreakingSpace]Module[{},
		Do[
		
			(*Model*)
			means = GenerateMeans[K,distance];
	
			(*Calculating errors of stage 3*)
			BayesPi=Stage3BDR[K,means,sigma];
			(*Classifiers*)
			clasifP = {};
			Do[AppendTo[clasifP,a],{a,1,K}];
			Print[Style["CHARACTERISTICS OF THE PROBLEM",Bold]];
			Print["- ",K," classes and mixture components which follow Gaussian distributions N(\[Mu],\[Sigma])."];
			Print["- ",Subscript["e","B"],": ",  N[BayesPi[[1]],5]," (Bayes error)."];
			Print["- The distance between the means of two adjacent components is ",distance,"."];
			Print["- \[Sigma] is equal to ", sigma,"." ];
			Print["- P(l,",Infinity,") for l={0,...",maxL "} is approximated by means of a Monte Carlo method (",nRep, "rep.)."];
			Print["- The possible correspondences \[Pi] between components and clases are:", Permutations[clasifP]];
			Print[Style["PROBABILITY OF ERROR[VOTING]",{Red,Bold}],"   Pv(l,",Infinity,")=", Style["\[CapitalSigma]",FontSize-> 36]," P(",Subscript["\[CapitalSigma]","l"],"=\[Pi]) P(errBDR|\[Pi])"];
			Print[Style["PROBABILITY OF ERROR[PCSSL]",{Blue,Bold}],"   P(l,",Infinity,")=", Style["\[CapitalSigma]",FontSize-> 36]," P(",Subscript["\[CapitalPi]","l"],"=\[Pi]) P(errBDR|\[Pi])"];
			Print[Style["Probability of error given a correspondence \[Pi]",Black]];
			Print["P(errBDR|\[Pi]): ", N[BayesPi,5]];
			Print[Style["Probability of a correspondence \[Pi] with l labelled examples",Black]];

			(*Probability of error of both procedures*)
			errorVOTING ={};
			errorPCSSL ={};

			(*Simulation of the data*)
			Do[(*l:0-maxL*)
				errorV = 0;
				errorP =0;
				probPermutationV= {};
				Do[AppendTo[probPermutationV,0],{a,1,K!}];
				probPermutationP= {};
				Do[AppendTo[probPermutationP,0],{a,1,K!}];

				Do[(*r1:1-nRep*)
					classifierVOTING = 0;
					classifierPCSSL =0;		
					If[l==0,
						(*l==0*)
						classif = RandomInteger[{1,K!}];
						classifierVOTING = classif;
						classifierPCSSL = classif; (*FIN l==0*),
						(*l>0*)
						randomizer = Index2Permutation[RandomInteger[{1,K!}],K];
						Ci = GenerateData[K,l,means,sigma, randomizer];
						(*Linear assignment problem*)
						VOTCM = CreateVOTINGCostMatrix[Ci,means];
						PCCM =CreatePCSSLCostMatrix[Ci, means,sigma];classifierVOTING= Permutation2Index[Permute[Position[Hungarian[VOTCM,True],1][[All,2]],InversePermutation[randomizer]]];
						classifierPCSSL= Permutation2Index[Permute[Position[Hungarian[PCCM,True],1][[All,2]],InversePermutation[randomizer]]](*FIN l>0*)
					];(*Fi*)

					(*ERRORS*)
					probPermutationV[[classifierVOTING]]++; 
					errorV += BayesPi[[classifierVOTING]];
					probPermutationP[[classifierPCSSL]]++; 
					errorP += BayesPi[[classifierPCSSL]];
				,{r1,1,nRep}];

				probPermutationV /=nRep;
				probPermutationP /=nRep;
				Print[Style["[V]",Red],"P(",Subscript["\[CapitalSigma]",l],"=\[Pi]): ", N[probPermutationV,5]];
				Print[Style["[P]",Blue],"P(",Subscript["\[CapitalPi]",l],"=\[Pi]): ", N[probPermutationP,5]];
				errorV /= nRep;
				errorP /= nRep;
				AppendTo[errorVOTING,errorV];
				AppendTo[errorPCSSL,errorP];
			,{l,0,maxL}];
			
			(*Bayes Error*)
			errorEB = {};
			Do[AppendTo[errorEB,N[BayesPi[[1]],5]],{i,1,maxL+1}];

			Print[Style["Probability of error (VOTING)",Red]];
			Print["Pv(l,",Infinity,"):", N[errorVOTING,5]];
			Print[Style["Probability of error (PCSSL)",Blue]];
			Print["P(l,",Infinity,"):", N[errorPCSSL,5]];

			Print[Style["ILLUSTRATION OF THE VARIATION OF THE PROBABILITIES OF ERROR",Bold]];
			Print[ListPlot[{N[errorVOTING],N[errorPCSSL],N[errorEB]},Joined->True,PlotLegends->{"VOTING","PCSSL","Bayes Error"}, PlotRange -> {0,1},DataRange->{0,maxL},PlotStyle-> {{Thick,Red},{Thick,Blue},{Thick,Black}}]];
		,{1}]];
\[NonBreakingSpace]\[NonBreakingSpace]
(************************************
Probability of error with zero eB
*************************************)
	ZeroEB[K_,maxL_]:= Module[{},
		Do[
			errorNoEB = {};
			Print[Style["PROBABILITY OF ERROR WHEN THE COMPONENTS ARE MUTUALLY DISJOINT (eB=0)",Bold]];
			Do[	
				error = 
					Sum[((K!*StirlingS2[l,c])/((K-c)!*K^l))*(1-((c+1)/(K)))
					,{c,0,Min[K-2,l]}];
				AppendTo[errorNoEB,error]
			,{l,0,maxL}];
			Print[Style["Probability of error of ",Green],Style[K,Green],Style[" classes",Green]];
			Print["P(l,",Infinity,"):", N[errorNoEB,5]];
			Print[Style["ILLUSTRATION OF THE VARIATION OF THE PROBABILITIES OF ERROR",Bold]];
			Print[ListPlot[{N[errorNoEB]},Joined->True,AxesOrigin->{1,0}, PlotRange -> {0,1},PlotStyle-> {{Thick,Green}}]];
		,{1}]];

(************************************
l_k with priors equiprobable
*************************************)

	LKEQ[K_] := N[Piecewise[
				{{0,K<2},{1,K==2}},
				(1/K^(K-2))*Sum[(-1)^j*Binomial[K,j](K-j)^(K-2)(K-1 + (K-j)/j)(j-1),{j,1,K-1}]]];

	LKEQPlot[max_]:= Module[{},
		Do[
			lks = {};
			Do[AppendTo[lks,LKEQ[k]],{k,0,max}];
			Print[ListPlot[lks,Joined->True,PlotStyle -> Thick, AxesLabel-> {"Number of classes","Expected number of labelled data"},PlotRange -> {0,Max[lks]},PlotLabel -> "l_k",AxesOrigin->{1,0}]]
		,{1}]];

(************************************
l_k with one prior no equiprobable
*************************************)

	LKPriors[priors_,nRepMC_] := Module[{},
		Do[
			value=0;
			CMD={};
			accumulation=0;
			Do[accumulation += priors[[b]];
				AppendTo[CMD,accumulation]
			,{b,1,Length[priors]}];
			Do[
				extractions =0;
				differentclasses =0;
				classes = {};
				Do[AppendTo[classes,0],{numC,1, Length[priors]}];
				NotFinish=True;
				While[NotFinish,
					x =RandomReal[];
					c = 1;
					While[x> CMD[[c]],c++];
					class = c;
					extractions+=1;
					If[classes[[c]]==0, classes[[c]]=1;differentclasses+=1,Null];
					If[differentclasses== Length[priors]-1,NotFinish=False,Null];
				];
				value += extractions;
			,{a,1,nRepMC}];
			value=N[value/nRepMC];
			Return[value];
		,{1}]];

(************************************
l_ 3
*************************************)

	L3Value[n1_,n2_,n3_]:= Module[{},2 + n1^2/(1-n1)+ n2^2/(1-n2)+ n3^2/(1-n3)];

	L3Plot[] := Module[{},Do[
			Print[Plot[L3Value[nk,(1-nk)/2,(1-nk)/2],{nk,0,1},PlotStyle -> Thick, AxesLabel-> {"Probability of n_1","Expected number of labelled data"},PlotLabel -> "l_k",PlotRange->{0,100}]]
		,{1}]];

(************************************
l_k for one population
*************************************)

	  LKSampling[K_, samplesize_, nRep_, folder_]:= Module[{},
		Do[
			SetDirectory[NotebookDirectory[]];
			t={};
			t=Timing[
			results ={};
			sample={};
			priors = {};
			Do[AppendTo[priors,1],{i,1,K}];
			sample=RandomVariate[\[ScriptD]=DirichletDistribution[priors],samplesize];
			Do[
				AppendTo[sample[[i]], 1- Total[sample[[i]]]]
			,{i,1,Length[sample]}];

			Do[
				aux = {};
				AppendTo[aux,Variance[sample[[i]]]];
				AppendTo[aux,If[K==2,1,LKPriors[sample[[i]],nRep]]];
				AppendTo[results,aux];
			,{i,1,Length[sample]}];];
			Print[K,"-class problem with a sample size of ",samplesize," and ",nRep," repetitions - DONE! Time: ",t[[1]]," sec."];
			dirPreffix = Directory[]<>"/" <> folder <> "/";
			dirSuffix = ToString[K] <> "-" <> ToString[samplesize] <> "-" <> ToString[nRep]<> ".out";
			Export[dirPreffix <> "sample" <> dirSuffix,sample,"Table"];
			Export[dirPreffix <> "results" <> dirSuffix,results,"Table"];
			Return[results];
		,{1}]];\[NonBreakingSpace]

End[]
EndPackage[]





































