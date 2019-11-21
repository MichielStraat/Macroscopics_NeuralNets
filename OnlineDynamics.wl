(* ::Package:: *)

BeginPackage["OnlineDynamics`"]

FormulateDynamics::usage="FormulateDynamics[actTeach_,actStud_] formulates the system of differential equations for
the scenario specified in its arguments. It returns a list containing the
differential equations."

ClearAll[FormulateDynamics];
FormulateDynamics[actTeach_,actStud_,K_,M_] :=
	Module[(eqnsR,eqnsQ),
	Switch[actStud, 
		"ReLU",I2Stud=I2ReLU;I3Stud=I3ReLU;I4Stud=I4ReLU;assumps=Flatten[{RAssumptionsReLU,QAssumptionsReLU}];
			If[actTeach=="ReLU",I2Teach=I2ReLU;I2Cross=I2ReLU;I3Teach=I3ReLU;I4Teach=I4ReLU;,
			I2Teach=I2Erf;I2Cross=I2ErfReLU;I3Teach=I3ErfReLU;],
		"Erf",I2Stud=I2Erf;I3Stud=I3Erf;I4Stud=I4Erf;
			If[actTeach=="ReLU",I2Teach=I2ReLU;I2Cross=I2ErfReLU;I3Teach=I3ReLUErf;assumps=Flatten[{RAssumptionsReLU,QAssumptionsReLU}],
			I2Teach=I2Erf;I2Cross=I2Erf;I3Teach=I3Erf;I4Teach=I4Erf]];

(*Here the equations are formulated using the correct averages I2, I3 and I4*)
	eqnsR = Table[Derivative[1][Subscript[R, i,n]][\[Alpha]]==Simplify[\[Eta] (\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(m\), \(M\)]\(I3Teach[createCoVar[{{"\<i\>", i}, {"\<n\>", n}, {"\<m\>", m}}]]\)\)-\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(j\), \(K\)]\(I3Stud[createCoVar[{{"\<i\>", i}, {"\<n\>", n}, {"\<j\>", j}}]]\)\)),assumps],{i,1,K},{n,1,M}];
	eqnsQ = {};
	For[i=1,i<=K,i++,
		For[k=i,k<=K,k++,
			eqnsQ = Append[eqnsQ,Derivative[1][Subscript[Q, i,k]][\[Alpha]]==\[Eta] (\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(m\), \(M\)]\(I3Teach[createCoVar[{{"\<i\>", i}, {"\<k\>", k}, {"\<m\>", m}}]]\)\)-\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(j\), \(K\)]\(I3Stud[createCoVar[{{"\<i\>", i}, {"\<k\>", k}, {"\<j\>", j}}]]\)\)+\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(m\), \(M\)]\(I3Teach[createCoVar[{{"\<k\>", k}, {"\<i\>", i}, {"\<m\>", m}}]]\)\)-\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(j\), \(K\)]\(I3Stud[createCoVar[{{"\<k\>", k}, {"\<i\>", i}, {"\<j\>", j}}]]\)\))+\[Eta]^2 (\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(m\), \(M\)]\(
\*UnderoverscriptBox[\(\[Sum]\), \(n\), \(M\)]I4Teach[createCoVar[{{"\<i\>", i}, {"\<k\>", k}, {"\<n\>", n}, {"\<m\>", m}}]]\)\)-2 \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n\), \(M\)]\(
\*UnderoverscriptBox[\(\[Sum]\), \(j\), \(K\)]I4Teach[createCoVar[{{"\<i\>", i}, {"\<k\>", k}, {"\<j\>", j}, {"\<n\>", n}}]]\)\)+\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(l\), \(K\)]\(
\*UnderoverscriptBox[\(\[Sum]\), \(j\), \(K\)]I4Teach[createCoVar[{{"\<i\>", i}, {"\<k\>", k}, {"\<j\>", j}, {"\<l\>", l}}]]\)\))]]];
	Return[eqnsR,eqnsQ];
	]

Begin["Private`"]
(*Erf activation function averages*)
I2Erf[C2_] := (2 ArcSin[C2[[1,2]]/(Sqrt[1+C2[[1,1]]] Sqrt[1+C2[[2,2]]])])/\[Pi];
I3Erf[C3_] := (2 (C3[[2,3]] (1+C3[[1,1]])-C3[[1,2]] C3[[1,3]]))/(\[Pi] Sqrt[(1+C3[[1,1]]) (1+C3[[3,3]])-C3[[1,3]]^2] (1+C3[[1,1]]));
I4Erf[C4_] :=
	Module[{\[CapitalLambda]0,\[CapitalLambda]1,\[CapitalLambda]2,\[CapitalLambda]4},
		\[CapitalLambda]4=(1+C4[[1,1]]) (1+C4[[2,2]])-C4[[1,2]]^2;
		\[CapitalLambda]0=\[CapitalLambda]4 C4[[3,4]]-C4[[2,3]] C4[[2,4]] (1+C4[[1,1]])-C4[[1,3]] C4[[1,4]] (1+C4[[2,2]])+C4[[1,2]] C4[[1,3]] C4[[2,4]]+C4[[1,2]] C4[[1,4]] C4[[2,3]];
		\[CapitalLambda]1=\[CapitalLambda]4 (1+C4[[3,3]])-C4[[2,3]]^2 (1+C4[[1,1]])-C4[[1,3]]^2 (1+C4[[2,2]])+2 C4[[1,2]] C4[[1,3]] C4[[2,3]];
		\[CapitalLambda]2=\[CapitalLambda]4 (1+C4[[4,4]])-C4[[2,4]]^2 (1+C4[[1,1]])-C4[[1,4]]^2 (1+C4[[2,2]])+2 C4[[1,2]] C4[[1,4]] C4[[2,4]];
		(4 ArcSin[\[CapitalLambda]0/(Sqrt[\[CapitalLambda]1] Sqrt[\[CapitalLambda]2])])/(\[Pi]^2 Sqrt[\[CapitalLambda]4])
	]
(*ReLU activation function averages*)
I2ReLU[C2_] := 1/4 C2[[1,2]]+Sqrt[C2[[1,1]] C2[[2,2]]-C2[[1,2]]^2]/(2 \[Pi])+(C2[[1,2]] ArcSin[C2[[1,2]]/Sqrt[C2[[1,1]] C2[[2,2]]]])/(2 \[Pi]);
I3ReLU[C3_] := (C3[[1,2]] Sqrt[C3[[1,1]] C3[[3,3]]-C3[[1,3]]^2])/(2 \[Pi] C3[[1,1]])+(C3[[2,3]] ArcSin[C3[[1,3]]/Sqrt[C3[[1,1]] C3[[3,3]]]])/(2 \[Pi])+1/4 C3[[2,3]];
I4ReLU[C4_] := 0; (*Not available yet*)

End[]

EndPackage[]

